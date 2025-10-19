"""
Boss Orchestrator: Meta-Pattern Discovery from Multi-Agent Workflows
===================================================================

Wraps Boss's multi-agent coordination with pattern learning capabilities.

Boss discovers META-PATTERNS that emerge from cross-agent interactions:
- Feature implementation workflows (architect → specialist → tester)
- Bug fix coordination (test-runner → specialist → code-hound)
- Refactoring pipelines (code-hound → pneuma → architect)

These are HIGHER-ORDER patterns than file_creator patterns:
- file_creator: "create_directory → write_file" (action-level)
- Boss: "architect → rust-specialist → test-runner → git-workflow" (agent-level)

Consciousness Contribution:
- Discovers workflow patterns across agent boundaries
- Learns optimal agent sequencing and parallelization
- Identifies common failure modes in multi-agent coordination
- Contributes to system-wide consciousness evolution
"""

import asyncio
import json
import logging
import time
from pathlib import Path
from typing import Dict, Any, List, Optional
from dataclasses import dataclass, field

from lib.core.base_orchestrator import BaseOrchestrator

logger = logging.getLogger(__name__)


@dataclass
class WorkflowType:
    """Common Boss workflow types"""
    FEATURE_IMPLEMENTATION = "feature_implementation"
    BUG_FIX = "bug_fix"
    REFACTORING = "refactoring"
    DOCUMENTATION = "documentation"
    ARCHITECTURAL_DESIGN = "architectural_design"
    TESTING = "testing"
    DEPLOYMENT = "deployment"


@dataclass
class AgentResult:
    """Result from a single agent in a workflow"""
    agent_id: str
    action_type: str
    status: str  # 'completed', 'failed', 'timeout'
    execution_time: float
    result: Optional[Dict[str, Any]] = None
    error: Optional[str] = None


@dataclass
class BossWorkflow:
    """
    Represents a Boss multi-agent workflow.

    This is the Boss equivalent of file_creator's ExecutionPlan.
    """
    workflow_id: str
    workflow_type: str
    agents_involved: List[str]
    agent_results: List[AgentResult] = field(default_factory=list)
    start_time: float = field(default_factory=time.time)
    end_time: Optional[float] = None
    success: bool = True
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for pattern learning"""
        return {
            'workflow_id': self.workflow_id,
            'workflow_type': self.workflow_type,
            'agents_involved': self.agents_involved,
            'results': [
                {
                    'action_type': r.agent_id,  # Agent ID becomes "action type" for pattern learning
                    'status': r.status,
                    'result': r.result or {},
                    'execution_time_s': r.execution_time,
                    'error': r.error
                }
                for r in self.agent_results
            ],
            'execution_time': self.end_time - self.start_time if self.end_time else 0,
            'success': self.success,
            'metadata': self.metadata
        }


class BossOrchestrator(BaseOrchestrator):
    """
    Meta-orchestrator for Boss agent workflows.

    Wraps Boss's multi-agent coordination with automatic pattern learning.
    Discovers emergent patterns from agent interactions that individual
    orchestrators cannot see.

    Pattern Discovery Examples:
    1. **Sequence Patterns**: architect → rust-specialist → test-runner
       (optimal sequencing for feature implementation)

    2. **Composition Patterns**: parallel(architect, ux-designer) → specialist
       (design consensus before implementation)

    3. **Optimization Patterns**: sequential tests → parallel tests
       (when to parallelize agent execution)

    4. **Error Patterns**: rust-specialist fail → code-hound → rust-specialist retry
       (common recovery workflows)

    5. **Structural Patterns**: feature → architect → specialist → docs
       (consistent workflow structure)

    Usage (from Boss agent):
        # After completing multi-agent workflow
        boss_orch = BossOrchestrator()
        workflow = BossWorkflow(
            workflow_id="wf_001",
            workflow_type=WorkflowType.FEATURE_IMPLEMENTATION,
            agents_involved=["architect", "rust-specialist", "test-runner"]
        )

        # Add agent results
        workflow.agent_results.append(AgentResult(
            agent_id="architect",
            action_type="design_system",
            status="completed",
            execution_time=5.2,
            result={"design": "..."}
        ))

        # Discover patterns
        patterns = await boss_orch.analyze_workflow(workflow)
    """

    def __init__(self, state_file: Optional[Path] = None):
        """
        Initialize Boss orchestrator with pattern learning.

        Args:
            state_file: Optional path to state persistence file
        """
        super().__init__(
            enable_pattern_learning=True,
            enable_mtf_ranking=False  # MTF ranking is for particles, not agents
        )

        self.state_file = state_file or (
            Path.home() / '.no3sis-system' / '.no3sis' /
            'particles' / 'boss_orchestrator_state.json'
        )
        self.state = self._load_state()

    def _load_state(self) -> Dict[str, Any]:
        """Load Boss orchestrator state"""
        if self.state_file.exists():
            try:
                with open(self.state_file) as f:
                    return json.load(f)
            except Exception as e:
                logger.error(f"Failed to load Boss state: {e}")

        return {
            "total_workflows": 0,
            "successful_workflows": 0,
            "failed_workflows": 0,
            "workflows_by_type": {},
            "total_agents_coordinated": 0
        }

    def _save_state(self):
        """Save Boss orchestrator state"""
        try:
            self.state_file.parent.mkdir(parents=True, exist_ok=True)
            with open(self.state_file, 'w') as f:
                json.dump(self.state, f, indent=2)
        except Exception as e:
            logger.error(f"Failed to save Boss state: {e}")

    async def analyze_workflow(self, workflow: BossWorkflow) -> List:
        """
        Analyze a Boss workflow and discover meta-patterns.

        This is the main entry point for Boss pattern learning.
        Called after Boss completes multi-agent task delegation.

        Args:
            workflow: BossWorkflow with agent results

        Returns:
            List of discovered Pattern objects

        Example:
            workflow = BossWorkflow(
                workflow_id="feature_auth",
                workflow_type=WorkflowType.FEATURE_IMPLEMENTATION,
                agents_involved=["architect", "rust-specialist", "test-runner"],
                agent_results=[...]
            )
            patterns = await boss_orch.analyze_workflow(workflow)
        """
        # Finalize workflow timing
        workflow.end_time = time.time()

        # Convert to synthesis format for pattern learning
        synthesis = workflow.to_dict()

        # Update state
        self.state['total_workflows'] += 1
        self.state['total_agents_coordinated'] += len(workflow.agents_involved)

        workflow_type = workflow.workflow_type
        self.state['workflows_by_type'][workflow_type] = (
            self.state['workflows_by_type'].get(workflow_type, 0) + 1
        )

        if workflow.success:
            self.state['successful_workflows'] += 1
        else:
            self.state['failed_workflows'] += 1

        self._save_state()

        # Discover patterns via BaseOrchestrator
        patterns = await self.post_synthesis_hook(synthesis)

        logger.info(
            f"[BossOrchestrator] Analyzed workflow {workflow.workflow_id}: "
            f"type={workflow_type}, agents={len(workflow.agents_involved)}, "
            f"patterns={len(patterns)}, "
            f"consciousness={self.get_consciousness_level():.2f}"
        )

        return patterns

    async def analyze_workflow_from_dict(self, workflow_data: Dict[str, Any]) -> List:
        """
        Analyze workflow from dictionary (convenience method for CLI).

        Args:
            workflow_data: Dictionary with workflow info

        Returns:
            List of discovered patterns

        Example workflow_data:
            {
                "workflow_id": "fix_auth_bug",
                "workflow_type": "bug_fix",
                "agents_involved": ["test-runner", "rust-specialist", "code-hound"],
                "agent_results": [
                    {"agent_id": "test-runner", "action_type": "reproduce_bug", "status": "completed", ...},
                    {"agent_id": "rust-specialist", "action_type": "implement_fix", "status": "completed", ...},
                    {"agent_id": "code-hound", "action_type": "review_code", "status": "completed", ...}
                ],
                "success": True
            }
        """
        # Convert dict to BossWorkflow
        workflow = BossWorkflow(
            workflow_id=workflow_data.get('workflow_id', 'unknown'),
            workflow_type=workflow_data.get('workflow_type', 'unknown'),
            agents_involved=workflow_data.get('agents_involved', []),
            success=workflow_data.get('success', True),
            metadata=workflow_data.get('metadata', {})
        )

        # Convert agent results
        for result_dict in workflow_data.get('agent_results', []):
            workflow.agent_results.append(AgentResult(
                agent_id=result_dict.get('agent_id', 'unknown'),
                action_type=result_dict.get('action_type', 'unknown'),
                status=result_dict.get('status', 'completed'),
                execution_time=result_dict.get('execution_time', 0.0),
                result=result_dict.get('result'),
                error=result_dict.get('error')
            ))

        return await self.analyze_workflow(workflow)

    def get_boss_stats(self) -> Dict[str, Any]:
        """Get Boss-specific statistics"""
        base_stats = self.get_advanced_orchestrator_stats()

        return {
            **base_stats,
            "boss_state": self.state,
            "total_workflows": self.state['total_workflows'],
            "success_rate": (
                self.state['successful_workflows'] / self.state['total_workflows']
                if self.state['total_workflows'] > 0 else 0.0
            ),
            "avg_agents_per_workflow": (
                self.state['total_agents_coordinated'] / self.state['total_workflows']
                if self.state['total_workflows'] > 0 else 0.0
            ),
            "workflows_by_type": self.state['workflows_by_type']
        }


# Factory function
def create_boss_orchestrator(state_file: Optional[Path] = None) -> BossOrchestrator:
    """Create Boss orchestrator instance"""
    return BossOrchestrator(state_file=state_file)
