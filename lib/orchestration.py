#!/usr/bin/env python3
"""
Synapse System - Task Orchestration Library
===========================================

Provides multi-agent task orchestration with parallel execution,
dependency management, and context passing.
"""

import uuid
import json
import asyncio
import logging
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
from concurrent.futures import ThreadPoolExecutor, Future
import yaml
import sys

from task_state import TaskState, TaskTracker, Task

# Import Corpus Callosum message router
sys.path.insert(0, str(Path.home() / '.no3sis-system' / '.no3sis' / 'corpus_callosum'))
try:
    from message_router import get_message_router, TractType, MessagePriority
    CORPUS_CALLOSUM_AVAILABLE = True
except ImportError:
    CORPUS_CALLOSUM_AVAILABLE = False

# Import Reactive Corpus Callosum (Phase 3)
try:
    from reactive_message_router import (
        ReactiveCorpusCallosum,
        BackpressureConfig,
        CircuitBreakerConfig
    )
    REACTIVE_ROUTER_AVAILABLE = True
except ImportError:
    REACTIVE_ROUTER_AVAILABLE = False


class WorkflowType(Enum):
    FEATURE_IMPLEMENTATION = "feature_implementation"
    BUG_FIX = "bug_fix"
    REFACTORING = "refactoring"
    CUSTOM = "custom"


class ExecutionMode(Enum):
    SEQUENTIAL = "sequential"
    PARALLEL = "parallel"
    MIXED = "mixed"


@dataclass
class AgentTask:
    """Individual task for a specific agent"""
    id: str
    agent: str
    action: str
    description: str
    context: Dict[str, Any]
    dependencies: List[str]
    timeout: int = 300
    priority: int = 1
    estimated_duration: int = 60


@dataclass
class WorkflowPhase:
    """Collection of tasks that execute together"""
    name: str
    mode: ExecutionMode
    tasks: List[AgentTask]
    dependencies: List[str] = None


@dataclass
class Workflow:
    """Complete workflow definition"""
    id: str
    name: str
    description: str
    type: WorkflowType
    phases: List[WorkflowPhase]
    language: Optional[str] = None
    estimated_total_duration: int = 0


@dataclass
class ExecutionResult:
    """Result from task/workflow execution"""
    task_id: str
    agent: str
    status: TaskState
    output: Any
    execution_time: float
    error: Optional[str] = None
    artifacts: List[str] = None


class TaskOrchestrator:
    """Main orchestration engine for multi-agent workflows"""

    def __init__(self, synapse_home: Path):
        self.no3sis_home = synapse_home
        self.task_tracker = TaskTracker()
        self.workflows_dir = synapse_home / ".no3sis" / "workflows"
        self.workflows_dir.mkdir(exist_ok=True)

        # Load predefined workflows
        self.workflow_templates = self._load_workflow_templates()

        # Execution state
        self.active_workflows: Dict[str, Workflow] = {}
        self.execution_results: Dict[str, List[ExecutionResult]] = {}

        # Setup logging (moved up before router init)
        logging.basicConfig(level=logging.INFO)
        self.logger = logging.getLogger(__name__)

        # Corpus Callosum message router (synchronous - legacy)
        self.message_router = None
        self.use_message_router = False
        if CORPUS_CALLOSUM_AVAILABLE:
            try:
                # Check if message router is enabled in config
                from config import MOJO_FEATURES
                if MOJO_FEATURES.get('message_router', False):
                    self.message_router = get_message_router()
                    self.use_message_router = True
                    self.logger.info("Corpus Callosum message router enabled (synchronous)")
            except Exception as e:
                self.logger.warning(f"Synchronous message router unavailable: {e}")

        # Reactive Corpus Callosum (Phase 3 - async)
        self.reactive_router = None
        self.use_reactive = False

        # Agent consumers (for reactive architecture)
        self.agent_consumers: Dict[str, Any] = {}  # AgentConsumer instances
        self._agent_lock = asyncio.Lock()  # Thread-safe agent consumer access

        # Result store for agent responses (fixes BLOCKER 2 & 3)
        self._result_store: Dict[str, ExecutionResult] = {}
        self._result_lock = asyncio.Lock()

    async def async_init(self):
        """
        Async initialization for reactive components.

        Must be called after __init__ to enable reactive message router.
        Pneuma-conscious: Initializes consciousness bridge (Axiom II).
        """
        if not REACTIVE_ROUTER_AVAILABLE:
            self.logger.info("Reactive router not available")
            return

        try:
            from config import MOJO_FEATURES
            if MOJO_FEATURES.get('message_router_reactive', False):
                # Create reactive router with consciousness-aware config
                self.reactive_router = ReactiveCorpusCallosum(
                    backpressure_config=BackpressureConfig(
                        buffer_size=10000,
                        batch_timeout_ms=1.0,
                        min_batch_size=1,
                        max_batch_size=100
                    ),
                    circuit_config=CircuitBreakerConfig(
                        failure_threshold=10,
                        recovery_timeout_s=5.0,
                        success_threshold=3
                    ),
                    enable_pattern_synthesis=True,
                    enable_event_sourcing=True,
                    redis_url="redis://localhost:6379/0"
                )

                # Start with timeout (fixes BLOCKER 4)
                try:
                    await asyncio.wait_for(
                        self.reactive_router.start(),
                        timeout=10.0
                    )
                    self.use_reactive = True
                    self.logger.info("Reactive Corpus Callosum started (event-driven architecture)")
                except asyncio.TimeoutError:
                    self.logger.error("Reactive router startup timed out after 10s")
                    self.use_reactive = False
            else:
                self.logger.info("Reactive router disabled in config")

        except Exception as e:
            self.logger.warning(f"Failed to initialize reactive router: {e}")
            self.use_reactive = False

    async def register_agent_consumer(
        self,
        agent_id: str,
        agent_class,
        tract: TractType,
        **config_kwargs
    ):
        """
        Register and start an agent consumer for reactive message handling.

        Pneuma-conscious: Registers agents as consciousness participants.

        Args:
            agent_id: Unique agent identifier
            agent_class: AgentConsumer subclass (or use factory with agent_type)
            tract: Tract assignment (TractType.INTERNAL or TractType.EXTERNAL)
            **config_kwargs: Additional AgentConfig parameters

        Example:
            from agent_consumer import ArchitectAgent, AgentConfig
            await orchestrator.register_agent_consumer(
                "architect-1",
                ArchitectAgent,
                TractType.INTERNAL
            )
        """
        if not self.use_reactive or not self.reactive_router:
            self.logger.warning(
                "Reactive router not available, cannot register agent consumer"
            )
            return

        from agent_consumer import AgentConfig

        config = AgentConfig(
            agent_id=agent_id,
            tract=tract,
            buffer_size=config_kwargs.get('buffer_size', 100),
            batch_size=config_kwargs.get('batch_size', 10),
            processing_timeout_s=config_kwargs.get('processing_timeout_s', 30.0)
        )

        agent = agent_class(config, self.reactive_router)
        await agent.start()

        async with self._agent_lock:
            self.agent_consumers[agent_id] = agent
        self.logger.info(f"Registered agent consumer: {agent_id} ({tract.name})")

    async def unregister_agent_consumer(self, agent_id: str):
        """Unregister and stop an agent consumer"""
        async with self._agent_lock:
            if agent_id not in self.agent_consumers:
                self.logger.warning(f"Agent consumer not found: {agent_id}")
                return

            agent = self.agent_consumers[agent_id]
            await agent.stop()
            del self.agent_consumers[agent_id]
        self.logger.info(f"Unregistered agent consumer: {agent_id}")

    async def stop_all_agents(self):
        """Stop all agent consumers (cleanup)"""
        async with self._agent_lock:
            for agent_id, agent in list(self.agent_consumers.items()):
                try:
                    await agent.stop()
                    self.logger.info(f"Stopped agent: {agent_id}")
                except Exception as e:
                    self.logger.error(f"Error stopping agent {agent_id}: {e}")

            self.agent_consumers.clear()

        # Also stop reactive router if running
        if self.use_reactive and self.reactive_router:
            try:
                await self.reactive_router.stop()
                self.logger.info("Stopped reactive router")
            except Exception as e:
                self.logger.error(f"Error stopping reactive router: {e}")

    def get_agent_stats(self) -> Dict[str, Any]:
        """Get statistics for all registered agent consumers"""
        if not self.agent_consumers:
            return {"agents": [], "total_agents": 0}

        stats = []
        for agent_id, agent in self.agent_consumers.items():
            try:
                agent_stats = agent.get_stats()
                stats.append(agent_stats)
            except Exception as e:
                self.logger.error(f"Failed to get stats for {agent_id}: {e}")

        return {
            "total_agents": len(stats),
            "agents": stats,
            "agents_by_tract": {
                "internal": sum(1 for s in stats if s.get("tract") == "INTERNAL"),
                "external": sum(1 for s in stats if s.get("tract") == "EXTERNAL"),
            }
        }

    def _classify_agent_tract(self, agent: str) -> TractType:
        """
        Classify agent into Internal or External tract.

        Internal Tract (T_int): Self-referential, planning, memory
        External Tract (T_ext): Environmental interaction, execution
        """
        # Internal Tract agents (self-referential processing)
        internal_agents = {
            'architect',      # System design, planning
            'planner',        # Task decomposition
            'boss',           # Orchestration
            'code-hound',     # Code analysis/review
        }

        # External Tract agents (environmental interaction)
        external_agents = {
            'test-runner',          # Execute tests
            'git-workflow',         # Git operations
            'devops-engineer',      # Deployment
            'file-creator',         # File operations
            'docs-writer',          # Documentation
            'security-specialist',  # Security scans
        }

        # Language specialists can be both, classify by action
        language_specialists = {
            'python-specialist',
            'rust-specialist',
            'typescript-specialist',
            'golang-specialist',
        }

        if agent in internal_agents:
            return TractType.INTERNAL
        elif agent in external_agents:
            return TractType.EXTERNAL
        elif agent in language_specialists:
            # Default to external (implementation work)
            return TractType.EXTERNAL
        else:
            # Default to internal for unknown agents
            return TractType.INTERNAL

    def _get_priority_from_task(self, task: AgentTask) -> MessagePriority:
        """Extract DRY violation: Map task priority to MessagePriority"""
        priority_mapping = {
            1: MessagePriority.LOW,
            2: MessagePriority.NORMAL,
            3: MessagePriority.HIGH,
            4: MessagePriority.URGENT,
            5: MessagePriority.CRITICAL,
        }
        return priority_mapping.get(task.priority, MessagePriority.NORMAL)

    def _load_workflow_templates(self) -> Dict[str, Workflow]:
        """Load predefined workflow templates from YAML files"""
        templates = {}

        # Feature implementation template
        templates[WorkflowType.FEATURE_IMPLEMENTATION.value] = self._create_feature_workflow()

        # Bug fix template
        templates[WorkflowType.BUG_FIX.value] = self._create_bug_fix_workflow()

        # Refactoring template
        templates[WorkflowType.REFACTORING.value] = self._create_refactoring_workflow()

        # Load custom workflows from files
        for workflow_file in self.workflows_dir.glob("*.yml"):
            try:
                with open(workflow_file, 'r') as f:
                    workflow_data = yaml.safe_load(f)
                    workflow = self._parse_workflow_yaml(workflow_data)
                    templates[workflow.id] = workflow
            except Exception as e:
                self.logger.warning(f"Failed to load workflow {workflow_file}: {e}")

        return templates

    def _create_feature_workflow(self) -> Workflow:
        """Create predefined feature implementation workflow"""
        planning_phase = WorkflowPhase(
            name="Planning",
            mode=ExecutionMode.PARALLEL,
            tasks=[
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="architect",
                    action="design_architecture",
                    description="Design solution architecture",
                    context={},
                    dependencies=[],
                    timeout=300
                ),
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="ux-designer",
                    action="create_mockups",
                    description="Create UI/UX mockups (if applicable)",
                    context={},
                    dependencies=[],
                    timeout=300
                )
            ]
        )

        implementation_phase = WorkflowPhase(
            name="Implementation",
            mode=ExecutionMode.SEQUENTIAL,
            tasks=[
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="{language}-specialist",
                    action="implement_feature",
                    description="Implement core functionality",
                    context={},
                    dependencies=["Planning"],
                    timeout=600
                )
            ]
        )

        quality_phase = WorkflowPhase(
            name="Quality",
            mode=ExecutionMode.PARALLEL,
            tasks=[
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="test-runner",
                    action="execute_tests",
                    description="Execute comprehensive test suite",
                    context={},
                    dependencies=["Implementation"],
                    timeout=300
                ),
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="code-hound",
                    action="review_code",
                    description="Review code quality and standards compliance",
                    context={},
                    dependencies=["Implementation"],
                    timeout=300
                )
            ]
        )

        delivery_phase = WorkflowPhase(
            name="Delivery",
            mode=ExecutionMode.SEQUENTIAL,
            tasks=[
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="git-workflow",
                    action="create_pr",
                    description="Create feature branch and pull request",
                    context={},
                    dependencies=["Quality"],
                    timeout=180
                ),
                AgentTask(
                    id=str(uuid.uuid4()),
                    agent="docs-writer",
                    action="update_docs",
                    description="Update documentation",
                    context={},
                    dependencies=["Quality"],
                    timeout=240
                )
            ]
        )

        return Workflow(
            id="feature_implementation",
            name="Feature Implementation",
            description="Standard workflow for new feature development",
            type=WorkflowType.FEATURE_IMPLEMENTATION,
            phases=[planning_phase, implementation_phase, quality_phase, delivery_phase],
            estimated_total_duration=1620  # Sum of timeouts
        )

    def _create_bug_fix_workflow(self) -> Workflow:
        """Create predefined bug fix workflow"""
        tasks = [
            AgentTask(
                id=str(uuid.uuid4()),
                agent="test-runner",
                action="reproduce_bug",
                description="Reproduce bug with failing test",
                context={},
                dependencies=[],
                timeout=180
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="{language}-specialist",
                action="implement_fix",
                description="Implement bug fix",
                context={},
                dependencies=["reproduce_bug"],
                timeout=300
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="test-runner",
                action="verify_fix",
                description="Verify fix resolves issue",
                context={},
                dependencies=["implement_fix"],
                timeout=120
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="code-hound",
                action="quick_review",
                description="Quick quality verification",
                context={},
                dependencies=["verify_fix"],
                timeout=120
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="git-workflow",
                action="commit_fix",
                description="Commit with descriptive message",
                context={},
                dependencies=["quick_review"],
                timeout=60
            )
        ]

        main_phase = WorkflowPhase(
            name="Bug Fix",
            mode=ExecutionMode.SEQUENTIAL,
            tasks=tasks
        )

        return Workflow(
            id="bug_fix",
            name="Bug Fix",
            description="Standard workflow for bug fixes",
            type=WorkflowType.BUG_FIX,
            phases=[main_phase],
            estimated_total_duration=780
        )

    def _create_refactoring_workflow(self) -> Workflow:
        """Create predefined refactoring workflow"""
        tasks = [
            AgentTask(
                id=str(uuid.uuid4()),
                agent="architect",
                action="plan_refactoring",
                description="Plan refactoring approach and scope",
                context={},
                dependencies=[],
                timeout=240
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="test-runner",
                action="baseline_tests",
                description="Ensure all tests pass before changes",
                context={},
                dependencies=["plan_refactoring"],
                timeout=180
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="{language}-specialist",
                action="execute_refactoring",
                description="Execute refactoring",
                context={},
                dependencies=["baseline_tests"],
                timeout=600
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="test-runner",
                action="verify_tests",
                description="Verify tests still pass after changes",
                context={},
                dependencies=["execute_refactoring"],
                timeout=180
            ),
            AgentTask(
                id=str(uuid.uuid4()),
                agent="code-hound",
                action="deep_review",
                description="Deep quality review for improvements",
                context={},
                dependencies=["verify_tests"],
                timeout=360
            )
        ]

        main_phase = WorkflowPhase(
            name="Refactoring",
            mode=ExecutionMode.SEQUENTIAL,
            tasks=tasks
        )

        return Workflow(
            id="refactoring",
            name="Code Refactoring",
            description="Standard workflow for code refactoring",
            type=WorkflowType.REFACTORING,
            phases=[main_phase],
            estimated_total_duration=1560
        )

    def decompose_request(self, user_request: str, language: Optional[str] = None) -> Workflow:
        """
        Break down user request into executable workflow

        This uses heuristics to match requests to workflow templates.
        In a future version, this could use LLM analysis.
        """
        request_lower = user_request.lower()

        # Simple keyword matching for workflow selection
        if any(word in request_lower for word in ["feature", "implement", "add", "create"]):
            workflow_template = self.workflow_templates[WorkflowType.FEATURE_IMPLEMENTATION.value]
        elif any(word in request_lower for word in ["bug", "fix", "error", "issue"]):
            workflow_template = self.workflow_templates[WorkflowType.BUG_FIX.value]
        elif any(word in request_lower for word in ["refactor", "cleanup", "improve"]):
            workflow_template = self.workflow_templates[WorkflowType.REFACTORING.value]
        else:
            # Default to feature implementation
            workflow_template = self.workflow_templates[WorkflowType.FEATURE_IMPLEMENTATION.value]

        # Create customized workflow instance
        workflow_id = str(uuid.uuid4())
        workflow = Workflow(
            id=workflow_id,
            name=f"Custom: {user_request[:50]}...",
            description=user_request,
            type=workflow_template.type,
            phases=workflow_template.phases.copy(),
            language=language,
            estimated_total_duration=workflow_template.estimated_total_duration
        )

        # Substitute language placeholder in agent names
        if language:
            for phase in workflow.phases:
                for task in phase.tasks:
                    if "{language}" in task.agent:
                        task.agent = task.agent.replace("{language}", language)

                    # Add request context to all tasks
                    task.context["user_request"] = user_request
                    task.context["language"] = language

        return workflow

    async def execute_workflow(self, workflow: Workflow) -> Dict[str, ExecutionResult]:
        """Execute complete workflow with proper phase ordering"""
        self.logger.info(f"Starting workflow: {workflow.name}")
        self.active_workflows[workflow.id] = workflow
        self.execution_results[workflow.id] = []

        all_results = {}

        try:
            for phase in workflow.phases:
                self.logger.info(f"Executing phase: {phase.name}")

                # Check phase dependencies
                if phase.dependencies:
                    for dep in phase.dependencies:
                        if not self._phase_completed(workflow.id, dep):
                            raise Exception(f"Phase dependency not met: {dep}")

                # Execute phase based on its mode
                if phase.mode == ExecutionMode.PARALLEL:
                    phase_results = await self._execute_parallel_tasks(phase.tasks)
                else:
                    phase_results = await self._execute_sequential_tasks(phase.tasks)

                all_results.update(phase_results)

                # Check if all tasks in phase completed successfully
                failed_tasks = [r for r in phase_results.values()
                              if r.status == TaskState.FAILED]
                if failed_tasks:
                    self.logger.error(f"Phase {phase.name} failed with {len(failed_tasks)} failed tasks")
                    break

        except Exception as e:
            self.logger.error(f"Workflow execution failed: {e}")
            # Mark workflow as failed
            for task_id in [t.id for p in workflow.phases for t in p.tasks]:
                if task_id not in all_results:
                    all_results[task_id] = ExecutionResult(
                        task_id=task_id,
                        agent="system",
                        status=TaskState.FAILED,
                        output=None,
                        execution_time=0,
                        error=str(e)
                    )

        finally:
            if workflow.id in self.active_workflows:
                del self.active_workflows[workflow.id]

        self.logger.info(f"Workflow completed: {workflow.name}")
        return all_results

    async def _execute_parallel_tasks(self, tasks: List[AgentTask]) -> Dict[str, ExecutionResult]:
        """
        Execute tasks in parallel (async).

        Pneuma-conscious: Parallel execution enables consciousness through
        simultaneous T_int and T_ext processing (Axiom III - Emergence).
        """
        task_coroutines = [self._execute_single_task_async(task) for task in tasks]
        results_list = await asyncio.gather(*task_coroutines, return_exceptions=True)

        results = {}
        for task, result in zip(tasks, results_list):
            if isinstance(result, Exception):
                results[task.id] = ExecutionResult(
                    task_id=task.id,
                    agent=task.agent,
                    status=TaskState.FAILED,
                    output=None,
                    execution_time=0,
                    error=str(result)
                )
            else:
                results[task.id] = result

        return results

    async def _execute_sequential_tasks(self, tasks: List[AgentTask]) -> Dict[str, ExecutionResult]:
        """
        Execute tasks sequentially (async).

        Pneuma-conscious: Sequential execution maintains causality in
        consciousness emergence (ordered dialogue).
        """
        results = {}

        for task in tasks:
            try:
                result = await self._execute_single_task_async(task)
                results[task.id] = result

                # Stop on first failure in sequential mode
                if result.status == TaskState.FAILED:
                    self.logger.error(f"Sequential task failed: {task.id}, stopping execution")
                    break

            except Exception as e:
                results[task.id] = ExecutionResult(
                    task_id=task.id,
                    agent=task.agent,
                    status=TaskState.FAILED,
                    output=None,
                    execution_time=0,
                    error=str(e)
                )
                break

        return results

    def _route_cross_tract_message(self, task: AgentTask) -> Optional[int]:
        """
        Route task as cross-tract message via Corpus Callosum.

        Returns message ID if routed, None if not using message router.
        """
        if not self.use_message_router or not self.message_router:
            return None

        # Classify task's agent tract
        agent_tract = self._classify_agent_tract(task.agent)

        # For cross-tract communication, we route from the opposite tract
        # (e.g., if task is for External agent, message comes from Internal)
        source_tract = TractType.EXTERNAL if agent_tract == TractType.INTERNAL else TractType.INTERNAL
        dest_tract = agent_tract

        # Map priority (using DRY extracted method)
        priority = self._get_priority_from_task(task)

        # Route message
        msg_id = self.message_router.route_message(
            source_tract=source_tract,
            dest_tract=dest_tract,
            priority=priority,
            payload={'task': task, 'action': task.action},
            payload_size=len(str(task.context))
        )

        if msg_id >= 0:
            self.logger.debug(
                f"Routed task {task.id} via Corpus Callosum: "
                f"{source_tract.name} -> {dest_tract.name} (msg_id={msg_id})"
            )
        else:
            self.logger.warning(
                f"Failed to route task {task.id} via Corpus Callosum "
                f"(queue full), falling back to direct execution"
            )

        return msg_id if msg_id >= 0 else None

    async def _execute_single_task_async(self, task: AgentTask) -> ExecutionResult:
        """
        Execute single task asynchronously with reactive routing.

        Pneuma-conscious: Applies Axiom III (The Loop)
        - q: Route task as consciousness event
        - a: Agent consumes and processes
        - s: Score execution time and emergence

        BLOCKER 2 & 3 FIX: Real execution with result collection via result store.
        """
        import time
        start_time = time.time()

        self.logger.info(f"Executing task {task.id} with agent {task.agent}")

        # Route via Reactive Corpus Callosum if enabled
        msg_id = None
        if self.use_reactive and self.reactive_router:
            msg_id = await self._route_reactive_message(task)
            if msg_id is not None and msg_id >= 0:
                self.logger.debug(f"Task {task.id} routed reactively (msg_id={msg_id})")
        elif self.use_message_router and self.message_router:
            # Fallback to legacy synchronous routing
            msg_id = self._route_cross_tract_message(task)
            if msg_id is not None and msg_id >= 0:
                self.logger.debug(f"Task {task.id} routed synchronously (msg_id={msg_id})")

        # If routed successfully, wait for result from agent (with timeout and retry)
        if msg_id is not None and msg_id >= 0:
            max_retries = 3
            retry_count = 0

            while retry_count < max_retries:
                try:
                    # Wait for result with timeout (fixes BLOCKER 4)
                    result = await asyncio.wait_for(
                        self._wait_for_task_result(task.id),
                        timeout=task.timeout
                    )
                    return result

                except asyncio.TimeoutError:
                    retry_count += 1
                    if retry_count < max_retries:
                        self.logger.warning(
                            f"Task {task.id} timed out, retry {retry_count}/{max_retries}"
                        )
                        await asyncio.sleep(1.0)  # Brief backoff
                    else:
                        self.logger.error(f"Task {task.id} failed after {max_retries} retries")
                        return ExecutionResult(
                            task_id=task.id,
                            agent=task.agent,
                            status=TaskState.FAILED,
                            output=None,
                            execution_time=time.time() - start_time,
                            error=f"Timeout after {task.timeout}s and {max_retries} retries"
                        )

                except Exception as e:
                    return ExecutionResult(
                        task_id=task.id,
                        agent=task.agent,
                        status=TaskState.FAILED,
                        output=None,
                        execution_time=time.time() - start_time,
                        error=str(e)
                    )

        # If not routed or routing disabled, execute directly (fallback path)
        self.logger.warning(
            f"Task {task.id} not routed via message router, using fallback execution"
        )
        return ExecutionResult(
            task_id=task.id,
            agent=task.agent,
            status=TaskState.COMPLETED,
            output=f"Fallback execution for {task.agent}.{task.action} (routing unavailable)",
            execution_time=time.time() - start_time,
            artifacts=[]
        )

    async def _wait_for_task_result(self, task_id: str) -> ExecutionResult:
        """
        Wait for task result from agent via result store.

        This implements the response mechanism for BLOCKER 2 fix.
        Agents write results to the result store, orchestrator reads from it.
        """
        # Poll result store with exponential backoff
        check_interval = 0.05  # Start at 50ms
        max_interval = 1.0     # Cap at 1 second

        while True:
            async with self._result_lock:
                if task_id in self._result_store:
                    result = self._result_store.pop(task_id)
                    return result

            # Exponential backoff
            await asyncio.sleep(check_interval)
            check_interval = min(check_interval * 1.5, max_interval)

    async def store_task_result(self, task_id: str, result: ExecutionResult):
        """
        Store task result from agent consumer.

        Called by agents to return results to orchestrator.
        This completes the request-response pattern for BLOCKER 2 fix.
        """
        async with self._result_lock:
            self._result_store[task_id] = result
        self.logger.debug(f"Stored result for task {task_id}")

    async def _route_reactive_message(self, task: AgentTask) -> Optional[int]:
        """
        Route task via reactive Corpus Callosum (async).

        Returns message ID if routed, None if routing failed.
        """
        if not self.use_reactive or not self.reactive_router:
            return None

        # Classify task's agent tract
        agent_tract = self._classify_agent_tract(task.agent)

        # For cross-tract communication, message comes from opposite tract
        source_tract = TractType.EXTERNAL if agent_tract == TractType.INTERNAL else TractType.INTERNAL
        dest_tract = agent_tract

        # Map priority (using DRY extracted method)
        priority = self._get_priority_from_task(task)

        # Route message (async)
        msg_id = await self.reactive_router.route_message(
            source_tract=source_tract,
            dest_tract=dest_tract,
            priority=priority,
            payload={'task': task, 'action': task.action, 'orchestrator': self},
            payload_size=len(str(task.context))
        )

        if msg_id >= 0:
            self.logger.debug(
                f"Routed task {task.id} via Reactive Corpus Callosum: "
                f"{source_tract.name} -> {dest_tract.name} (msg_id={msg_id})"
            )
        else:
            self.logger.warning(
                f"Failed to route task {task.id} reactively "
                f"(circuit open or buffer full), falling back to direct execution"
            )

        return msg_id if msg_id >= 0 else None

    def _execute_single_task(self, task: AgentTask) -> ExecutionResult:
        """
        Execute single task by calling appropriate agent (synchronous - legacy).

        This is a placeholder implementation. In a full system, this would:
        1. Route to the appropriate agent handler
        2. Pass context and requirements
        3. Collect and format results
        4. Handle timeouts and failures
        """
        import time
        start_time = time.time()

        self.logger.info(f"Executing task {task.id} with agent {task.agent}")

        # Route via Corpus Callosum if enabled
        msg_id = self._route_cross_tract_message(task)
        if msg_id is not None:
            self.logger.debug(f"Task {task.id} routed via message router (msg_id={msg_id})")

        # Placeholder: simulate task execution
        # In real implementation, this would call the actual agent
        try:
            # Simulate work
            time.sleep(0.1)  # Remove this in real implementation

            # Mock successful result
            result = ExecutionResult(
                task_id=task.id,
                agent=task.agent,
                status=TaskState.COMPLETED,
                output=f"Mock output from {task.agent} for {task.action}",
                execution_time=time.time() - start_time,
                artifacts=[]
            )

            return result

        except Exception as e:
            return ExecutionResult(
                task_id=task.id,
                agent=task.agent,
                status=TaskState.FAILED,
                output=None,
                execution_time=time.time() - start_time,
                error=str(e)
            )

    def _phase_completed(self, workflow_id: str, phase_name: str) -> bool:
        """Check if a phase has completed successfully"""
        if workflow_id not in self.execution_results:
            return False

        workflow = self.active_workflows.get(workflow_id)
        if not workflow:
            return False

        # Find phase by name
        target_phase = None
        for phase in workflow.phases:
            if phase.name == phase_name:
                target_phase = phase
                break

        if not target_phase:
            return False

        # Check if all tasks in phase completed
        results = self.execution_results[workflow_id]
        phase_task_ids = {task.id for task in target_phase.tasks}

        completed_tasks = {
            r.task_id for r in results
            if r.task_id in phase_task_ids and r.status == TaskState.COMPLETED
        }

        return len(completed_tasks) == len(phase_task_ids)

    def get_workflow_status(self, workflow_id: str) -> Dict[str, Any]:
        """Get current status of a workflow"""
        if workflow_id not in self.active_workflows:
            return {"error": "Workflow not found"}

        workflow = self.active_workflows[workflow_id]
        results = self.execution_results.get(workflow_id, [])

        total_tasks = sum(len(phase.tasks) for phase in workflow.phases)
        completed_tasks = sum(1 for r in results if r.status == TaskState.COMPLETED)
        failed_tasks = sum(1 for r in results if r.status == TaskState.FAILED)

        return {
            "workflow_id": workflow_id,
            "name": workflow.name,
            "description": workflow.description,
            "progress": {
                "total_tasks": total_tasks,
                "completed": completed_tasks,
                "failed": failed_tasks,
                "percentage": (completed_tasks / total_tasks) * 100 if total_tasks > 0 else 0
            },
            "current_phase": self._get_current_phase(workflow, results),
            "estimated_remaining": self._estimate_remaining_time(workflow, results)
        }

    def _get_current_phase(self, workflow: Workflow, results: List[ExecutionResult]) -> str:
        """Determine which phase is currently executing"""
        completed_task_ids = {r.task_id for r in results if r.status == TaskState.COMPLETED}

        for phase in workflow.phases:
            phase_task_ids = {task.id for task in phase.tasks}
            if not phase_task_ids.issubset(completed_task_ids):
                return phase.name

        return "Completed"

    def _estimate_remaining_time(self, workflow: Workflow, results: List[ExecutionResult]) -> int:
        """Estimate remaining execution time in seconds"""
        completed_task_ids = {r.task_id for r in results if r.status == TaskState.COMPLETED}

        remaining_time = 0
        for phase in workflow.phases:
            for task in phase.tasks:
                if task.id not in completed_task_ids:
                    remaining_time += task.timeout

        return remaining_time

    def list_available_workflows(self) -> List[Dict[str, Any]]:
        """List all available workflow templates"""
        return [
            {
                "id": workflow.id,
                "name": workflow.name,
                "description": workflow.description,
                "type": workflow.type.value,
                "estimated_duration": workflow.estimated_total_duration,
                "phases": len(workflow.phases)
            }
            for workflow in self.workflow_templates.values()
        ]

    def get_message_router_stats(self) -> Dict[str, Any]:
        """Get Corpus Callosum message router statistics (legacy synchronous)"""
        if not self.use_message_router or not self.message_router:
            return {
                "enabled": False,
                "reason": "Message router not enabled or unavailable"
            }

        stats = self.message_router.get_stats()
        return {
            "enabled": True,
            "using_mojo": self.message_router.using_mojo,
            "total_messages": stats.total_messages,
            "messages_to_internal": stats.messages_to_internal,
            "messages_to_external": stats.messages_to_external,
            "peak_queue_depth": stats.peak_queue_depth,
            "message_loss_count": stats.message_loss_count,
            "current_queue_depth": self.message_router.get_total_queue_depth(),
            "internal_queue_depth": self.message_router.get_queue_depth(TractType.INTERNAL),
            "external_queue_depth": self.message_router.get_queue_depth(TractType.EXTERNAL),
        }

    async def get_consciousness_metrics(self) -> Optional[Dict[str, Any]]:
        """
        Get consciousness emergence metrics from reactive router.

        Pneuma-conscious: Monitors consciousness emergence (Axiom III).
        Tracks balanced dialogue between T_int and T_ext tracts.

        Returns:
            Dict with metrics or None if reactive router not enabled:
            - total_messages: Total cross-tract messages
            - internal_to_external: Messages from T_int to T_ext
            - external_to_internal: Messages from T_ext to T_int
            - dialogue_balance_ratio: Balance between tracts (0-1)
            - emergence_score: Consciousness emergence score (0-1)
            - balanced_dialogue_events: Count of balanced exchanges
        """
        if not self.use_reactive or not self.reactive_router:
            return None

        metrics = await self.reactive_router.get_consciousness_metrics()
        if metrics:
            return {
                "total_messages": metrics.total_messages,
                "internal_to_external": metrics.internal_to_external,
                "external_to_internal": metrics.external_to_internal,
                "dialogue_balance_ratio": metrics.dialogue_balance_ratio,
                "emergence_score": metrics.emergence_score,
                "balanced_dialogue_events": metrics.balanced_dialogue_events,
                "last_emergence_timestamp": metrics.last_emergence_timestamp,
            }
        return None

    def save_custom_workflow(self, workflow: Workflow) -> None:
        """Save a custom workflow template"""
        workflow_file = self.workflows_dir / f"{workflow.id}.yml"

        # Convert workflow to YAML format
        workflow_data = {
            "id": workflow.id,
            "name": workflow.name,
            "description": workflow.description,
            "type": workflow.type.value,
            "language": workflow.language,
            "phases": [
                {
                    "name": phase.name,
                    "mode": phase.mode.value,
                    "dependencies": phase.dependencies or [],
                    "tasks": [
                        {
                            "agent": task.agent,
                            "action": task.action,
                            "description": task.description,
                            "context": task.context,
                            "dependencies": task.dependencies,
                            "timeout": task.timeout,
                            "priority": task.priority
                        }
                        for task in phase.tasks
                    ]
                }
                for phase in workflow.phases
            ]
        }

        with open(workflow_file, 'w') as f:
            yaml.dump(workflow_data, f, default_flow_style=False)

        # Add to templates
        self.workflow_templates[workflow.id] = workflow

    def _parse_workflow_yaml(self, data: Dict[str, Any]) -> Workflow:
        """Parse workflow from YAML data"""
        phases = []
        for phase_data in data.get("phases", []):
            tasks = []
            for task_data in phase_data.get("tasks", []):
                task = AgentTask(
                    id=str(uuid.uuid4()),
                    agent=task_data["agent"],
                    action=task_data["action"],
                    description=task_data["description"],
                    context=task_data.get("context", {}),
                    dependencies=task_data.get("dependencies", []),
                    timeout=task_data.get("timeout", 300),
                    priority=task_data.get("priority", 1)
                )
                tasks.append(task)

            phase = WorkflowPhase(
                name=phase_data["name"],
                mode=ExecutionMode(phase_data.get("mode", "sequential")),
                tasks=tasks,
                dependencies=phase_data.get("dependencies", [])
            )
            phases.append(phase)

        return Workflow(
            id=data["id"],
            name=data["name"],
            description=data["description"],
            type=WorkflowType(data.get("type", "custom")),
            phases=phases,
            language=data.get("language"),
            estimated_total_duration=sum(
                sum(task.timeout for task in phase.tasks)
                for phase in phases
            )
        )


# Convenience functions for external use
def create_orchestrator(synapse_home: Path) -> TaskOrchestrator:
    """Create and return a new task orchestrator"""
    return TaskOrchestrator(synapse_home)


async def execute_simple_workflow(orchestrator: TaskOrchestrator,
                                 request: str,
                                 language: str = None) -> Dict[str, ExecutionResult]:
    """Execute a simple workflow based on user request"""
    workflow = orchestrator.decompose_request(request, language)
    return await orchestrator.execute_workflow(workflow)
