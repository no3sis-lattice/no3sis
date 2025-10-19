#!/usr/bin/env python3
"""
Synapse System - Task State Management
======================================

Manages task lifecycle, state tracking, and execution history
for the orchestration system.
"""

import uuid
import json
import sqlite3
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Any, Union
from dataclasses import dataclass, asdict
from enum import Enum
import threading


class TaskState(Enum):
    """Task execution states"""
    PENDING = "pending"
    ASSIGNED = "assigned"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"
    VERIFIED = "verified"
    RETRY = "retry"


class TaskPriority(Enum):
    """Task priority levels"""
    LOW = 1
    NORMAL = 2
    HIGH = 3
    URGENT = 4
    CRITICAL = 5


@dataclass
class Task:
    """Individual task representation"""
    id: str
    workflow_id: str
    agent: str
    action: str
    description: str
    state: TaskState
    priority: TaskPriority
    context: Dict[str, Any]
    dependencies: List[str]
    created_at: datetime
    updated_at: datetime
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    timeout: int = 300
    retry_count: int = 0
    max_retries: int = 3
    result: Optional[Any] = None
    error: Optional[str] = None
    artifacts: List[str] = None

    def __post_init__(self):
        if self.artifacts is None:
            self.artifacts = []


@dataclass
class TaskHistory:
    """Historical record of task state changes"""
    task_id: str
    previous_state: TaskState
    new_state: TaskState
    timestamp: datetime
    agent: str
    notes: Optional[str] = None


class TaskTracker:
    """Manages task state and persistence"""

    def __init__(self, synapse_home: Path = None):
        if synapse_home is None:
            synapse_home = Path.home() / ".no3sis-system"

        self.db_path = synapse_home / ".no3sis" / "task_state.db"
        self.db_path.parent.mkdir(parents=True, exist_ok=True)

        # Thread-safe task cache
        self._tasks_cache: Dict[str, Task] = {}
        self._lock = threading.RLock()

        # Initialize database
        self._init_database()

    def _init_database(self):
        """Initialize SQLite database for task persistence"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS tasks (
                    id TEXT PRIMARY KEY,
                    workflow_id TEXT NOT NULL,
                    agent TEXT NOT NULL,
                    action TEXT NOT NULL,
                    description TEXT,
                    state TEXT NOT NULL,
                    priority INTEGER NOT NULL,
                    context TEXT,
                    dependencies TEXT,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL,
                    started_at TEXT,
                    completed_at TEXT,
                    timeout INTEGER DEFAULT 300,
                    retry_count INTEGER DEFAULT 0,
                    max_retries INTEGER DEFAULT 3,
                    result TEXT,
                    error TEXT,
                    artifacts TEXT
                )
            """)

            conn.execute("""
                CREATE TABLE IF NOT EXISTS task_history (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    task_id TEXT NOT NULL,
                    previous_state TEXT,
                    new_state TEXT NOT NULL,
                    timestamp TEXT NOT NULL,
                    agent TEXT,
                    notes TEXT,
                    FOREIGN KEY (task_id) REFERENCES tasks (id)
                )
            """)

            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_tasks_workflow_id ON tasks(workflow_id);
            """)

            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_tasks_state ON tasks(state);
            """)

            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_task_history_task_id ON task_history(task_id);
            """)

            conn.commit()

    def create_task(self,
                   workflow_id: str,
                   agent: str,
                   action: str,
                   description: str,
                   dependencies: List[str] = None,
                   priority: TaskPriority = TaskPriority.NORMAL,
                   context: Dict[str, Any] = None,
                   timeout: int = 300,
                   max_retries: int = 3) -> str:
        """Create a new task and return its ID"""

        if dependencies is None:
            dependencies = []
        if context is None:
            context = {}

        task_id = str(uuid.uuid4())
        now = datetime.now()

        task = Task(
            id=task_id,
            workflow_id=workflow_id,
            agent=agent,
            action=action,
            description=description,
            state=TaskState.PENDING,
            priority=priority,
            context=context,
            dependencies=dependencies,
            created_at=now,
            updated_at=now,
            timeout=timeout,
            max_retries=max_retries
        )

        with self._lock:
            # Add to cache
            self._tasks_cache[task_id] = task

            # Persist to database
            self._save_task_to_db(task)

            # Record initial state
            self._record_state_change(task_id, None, TaskState.PENDING, agent)

        return task_id

    def get_task(self, task_id: str) -> Optional[Task]:
        """Retrieve task by ID"""
        with self._lock:
            # Check cache first
            if task_id in self._tasks_cache:
                return self._tasks_cache[task_id]

            # Load from database
            task = self._load_task_from_db(task_id)
            if task:
                self._tasks_cache[task_id] = task

            return task

    def update_task_state(self,
                         task_id: str,
                         new_state: TaskState,
                         agent: str = "system",
                         result: Any = None,
                         error: str = None,
                         artifacts: List[str] = None,
                         notes: str = None) -> bool:
        """Update task state and record the change"""

        with self._lock:
            task = self.get_task(task_id)
            if not task:
                return False

            old_state = task.state
            task.state = new_state
            task.updated_at = datetime.now()

            # Update timing fields based on state
            if new_state == TaskState.IN_PROGRESS and not task.started_at:
                task.started_at = datetime.now()
            elif new_state in [TaskState.COMPLETED, TaskState.FAILED, TaskState.CANCELLED]:
                if not task.completed_at:
                    task.completed_at = datetime.now()

            # Update result/error
            if result is not None:
                task.result = result
            if error is not None:
                task.error = error
            if artifacts is not None:
                task.artifacts = artifacts

            # Handle retry logic
            if new_state == TaskState.RETRY:
                task.retry_count += 1
                if task.retry_count >= task.max_retries:
                    task.state = TaskState.FAILED
                    task.error = f"Max retries ({task.max_retries}) exceeded"

            # Update cache and database
            self._tasks_cache[task_id] = task
            self._save_task_to_db(task)

            # Record state change
            self._record_state_change(task_id, old_state, new_state, agent, notes)

            return True

    def get_tasks_by_workflow(self, workflow_id: str) -> List[Task]:
        """Get all tasks for a specific workflow"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("""
                SELECT * FROM tasks WHERE workflow_id = ? ORDER BY created_at
            """, (workflow_id,))

            tasks = []
            for row in cursor.fetchall():
                task = self._row_to_task(row)
                tasks.append(task)
                # Update cache
                with self._lock:
                    self._tasks_cache[task.id] = task

            return tasks

    def get_tasks_by_state(self, state: TaskState) -> List[Task]:
        """Get all tasks in a specific state"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("""
                SELECT * FROM tasks WHERE state = ? ORDER BY priority DESC, created_at
            """, (state.value,))

            tasks = []
            for row in cursor.fetchall():
                task = self._row_to_task(row)
                tasks.append(task)
                # Update cache
                with self._lock:
                    self._tasks_cache[task.id] = task

            return tasks

    def get_ready_tasks(self) -> List[Task]:
        """Get tasks that are ready to execute (dependencies satisfied)"""
        pending_tasks = self.get_tasks_by_state(TaskState.PENDING)
        ready_tasks = []

        for task in pending_tasks:
            if self._dependencies_satisfied(task):
                ready_tasks.append(task)

        # Sort by priority and creation time
        ready_tasks.sort(key=lambda t: (t.priority.value, t.created_at), reverse=True)
        return ready_tasks

    def _dependencies_satisfied(self, task: Task) -> bool:
        """Check if all task dependencies are completed"""
        if not task.dependencies:
            return True

        for dep_id in task.dependencies:
            dep_task = self.get_task(dep_id)
            if not dep_task or dep_task.state != TaskState.COMPLETED:
                return False

        return True

    def get_task_history(self, task_id: str) -> List[TaskHistory]:
        """Get state change history for a task"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("""
                SELECT task_id, previous_state, new_state, timestamp, agent, notes
                FROM task_history
                WHERE task_id = ?
                ORDER BY timestamp
            """, (task_id,))

            history = []
            for row in cursor.fetchall():
                prev_state = TaskState(row[1]) if row[1] else None
                hist = TaskHistory(
                    task_id=row[0],
                    previous_state=prev_state,
                    new_state=TaskState(row[2]),
                    timestamp=datetime.fromisoformat(row[3]),
                    agent=row[4],
                    notes=row[5]
                )
                history.append(hist)

            return history

    def get_workflow_summary(self, workflow_id: str) -> Dict[str, Any]:
        """Get summary statistics for a workflow"""
        tasks = self.get_tasks_by_workflow(workflow_id)

        if not tasks:
            return {"error": "Workflow not found"}

        state_counts = {}
        for state in TaskState:
            state_counts[state.value] = sum(1 for t in tasks if t.state == state)

        total_tasks = len(tasks)
        completed_tasks = state_counts.get(TaskState.COMPLETED.value, 0)
        failed_tasks = state_counts.get(TaskState.FAILED.value, 0)

        # Calculate timing statistics
        start_time = min(t.created_at for t in tasks)
        end_time = max(t.updated_at for t in tasks)
        duration = end_time - start_time

        # Estimate progress
        progress_percentage = (completed_tasks / total_tasks * 100) if total_tasks > 0 else 0

        return {
            "workflow_id": workflow_id,
            "total_tasks": total_tasks,
            "state_counts": state_counts,
            "progress_percentage": progress_percentage,
            "duration": duration.total_seconds(),
            "start_time": start_time.isoformat(),
            "end_time": end_time.isoformat(),
            "is_complete": completed_tasks + failed_tasks == total_tasks
        }

    def cleanup_old_tasks(self, days: int = 30) -> int:
        """Clean up tasks older than specified days"""
        cutoff_date = datetime.now() - timedelta(days=days)

        with sqlite3.connect(self.db_path) as conn:
            # Remove old task history first (foreign key constraint)
            cursor = conn.execute("""
                DELETE FROM task_history
                WHERE task_id IN (
                    SELECT id FROM tasks WHERE created_at < ?
                )
            """, (cutoff_date.isoformat(),))

            history_deleted = cursor.rowcount

            # Remove old tasks
            cursor = conn.execute("""
                DELETE FROM tasks WHERE created_at < ?
            """, (cutoff_date.isoformat(),))

            tasks_deleted = cursor.rowcount
            conn.commit()

        # Clear cache of deleted tasks
        with self._lock:
            self._tasks_cache.clear()

        return tasks_deleted

    def _save_task_to_db(self, task: Task):
        """Save task to database"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO tasks (
                    id, workflow_id, agent, action, description, state, priority,
                    context, dependencies, created_at, updated_at, started_at,
                    completed_at, timeout, retry_count, max_retries, result,
                    error, artifacts
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                task.id, task.workflow_id, task.agent, task.action, task.description,
                task.state.value, task.priority.value,
                json.dumps(task.context), json.dumps(task.dependencies),
                task.created_at.isoformat(), task.updated_at.isoformat(),
                task.started_at.isoformat() if task.started_at else None,
                task.completed_at.isoformat() if task.completed_at else None,
                task.timeout, task.retry_count, task.max_retries,
                json.dumps(task.result) if task.result else None,
                task.error,
                json.dumps(task.artifacts) if task.artifacts else None
            ))
            conn.commit()

    def _load_task_from_db(self, task_id: str) -> Optional[Task]:
        """Load task from database"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("SELECT * FROM tasks WHERE id = ?", (task_id,))
            row = cursor.fetchone()

            if row:
                return self._row_to_task(row)

            return None

    def _row_to_task(self, row) -> Task:
        """Convert database row to Task object"""
        return Task(
            id=row[0],
            workflow_id=row[1],
            agent=row[2],
            action=row[3],
            description=row[4],
            state=TaskState(row[5]),
            priority=TaskPriority(row[6]),
            context=json.loads(row[7]) if row[7] else {},
            dependencies=json.loads(row[8]) if row[8] else [],
            created_at=datetime.fromisoformat(row[9]),
            updated_at=datetime.fromisoformat(row[10]),
            started_at=datetime.fromisoformat(row[11]) if row[11] else None,
            completed_at=datetime.fromisoformat(row[12]) if row[12] else None,
            timeout=row[13],
            retry_count=row[14],
            max_retries=row[15],
            result=json.loads(row[16]) if row[16] else None,
            error=row[17],
            artifacts=json.loads(row[18]) if row[18] else []
        )

    def _record_state_change(self,
                           task_id: str,
                           old_state: Optional[TaskState],
                           new_state: TaskState,
                           agent: str,
                           notes: str = None):
        """Record task state change in history"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT INTO task_history (
                    task_id, previous_state, new_state, timestamp, agent, notes
                ) VALUES (?, ?, ?, ?, ?, ?)
            """, (
                task_id,
                old_state.value if old_state else None,
                new_state.value,
                datetime.now().isoformat(),
                agent,
                notes
            ))
            conn.commit()

    def export_workflow_data(self, workflow_id: str) -> Dict[str, Any]:
        """Export complete workflow data including tasks and history"""
        tasks = self.get_tasks_by_workflow(workflow_id)

        export_data = {
            "workflow_id": workflow_id,
            "export_timestamp": datetime.now().isoformat(),
            "summary": self.get_workflow_summary(workflow_id),
            "tasks": [],
            "history": {}
        }

        for task in tasks:
            task_data = asdict(task)
            # Convert datetime objects to ISO strings
            for field in ["created_at", "updated_at", "started_at", "completed_at"]:
                if task_data[field]:
                    task_data[field] = task_data[field].isoformat()

            # Convert enums to strings
            task_data["state"] = task_data["state"].value
            task_data["priority"] = task_data["priority"].value

            export_data["tasks"].append(task_data)

            # Get task history
            history = self.get_task_history(task.id)
            export_data["history"][task.id] = [
                {
                    "previous_state": h.previous_state.value if h.previous_state else None,
                    "new_state": h.new_state.value,
                    "timestamp": h.timestamp.isoformat(),
                    "agent": h.agent,
                    "notes": h.notes
                }
                for h in history
            ]

        return export_data


# Convenience functions
def create_task_tracker(synapse_home: Path = None) -> TaskTracker:
    """Create and return a new task tracker"""
    return TaskTracker(synapse_home)


def get_task_metrics(tracker: TaskTracker, workflow_id: str = None) -> Dict[str, Any]:
    """Get task execution metrics"""
    if workflow_id:
        return tracker.get_workflow_summary(workflow_id)

    # Global metrics across all workflows
    metrics = {
        "total_pending": len(tracker.get_tasks_by_state(TaskState.PENDING)),
        "total_in_progress": len(tracker.get_tasks_by_state(TaskState.IN_PROGRESS)),
        "total_completed": len(tracker.get_tasks_by_state(TaskState.COMPLETED)),
        "total_failed": len(tracker.get_tasks_by_state(TaskState.FAILED)),
        "ready_to_execute": len(tracker.get_ready_tasks())
    }

    return metrics