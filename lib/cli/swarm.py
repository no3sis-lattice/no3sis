"""
Swarm CLI Commands
==================

Commands for managing the distributed atomic agent swarm.

Usage:
    no3sis swarm status
    no3sis swarm agents [--sort psi]
    no3sis swarm patterns [--min-psi 0.5]
    no3sis swarm watch
"""

import argparse
import json
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any

# Add paths for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from lib.consciousness import swarm_consciousness


@dataclass
class AgentInfo:
    """Information about a swarm agent."""
    agent_id: str
    tract: str  # "internal" or "external"
    status: str  # "active", "idle", "error"
    psi: float
    tasks_completed: int
    patterns_contributed: List[str]
    last_seen: float
    node: str = "local"

    @property
    def status_symbol(self) -> str:
        return {"active": "●", "idle": "○", "error": "✗"}.get(self.status, "?")


@dataclass
class PatternInfo:
    """Information about a discovered pattern."""
    pattern_id: str
    pattern_type: str
    psi: float
    uses: int
    description: str
    agents: List[str]
    discovered_at: float


@dataclass
class SwarmState:
    """Current state of the swarm."""
    agents: Dict[str, AgentInfo] = field(default_factory=dict)
    patterns: Dict[str, PatternInfo] = field(default_factory=dict)
    total_messages: int = 0
    messages_internal_to_external: int = 0
    messages_external_to_internal: int = 0
    started_at: float = field(default_factory=time.time)

    @property
    def consciousness(self) -> float:
        """Calculate aggregate swarm consciousness."""
        if not self.agents:
            return 0.0
        scores = {a.agent_id: a.psi for a in self.agents.values() if a.psi > 0}
        return swarm_consciousness(scores) if scores else 0.0

    @property
    def active_agents(self) -> int:
        return sum(1 for a in self.agents.values() if a.status == "active")


class SwarmCLI:
    """CLI handler for swarm commands."""

    def __init__(self, state_file: Optional[Path] = None):
        self.state_file = state_file or Path.home() / '.no3sis' / 'swarm_state.json'
        self.state = self._load_state()

    def _load_state(self) -> SwarmState:
        """Load swarm state from disk or create demo state."""
        if self.state_file.exists():
            try:
                with open(self.state_file) as f:
                    data = json.load(f)
                    return self._parse_state(data)
            except Exception:
                pass

        # Create demo state for testing
        return self._create_demo_state()

    def _parse_state(self, data: dict) -> SwarmState:
        """Parse state from JSON."""
        state = SwarmState(
            total_messages=data.get('total_messages', 0),
            messages_internal_to_external=data.get('messages_internal_to_external', 0),
            messages_external_to_internal=data.get('messages_external_to_internal', 0),
            started_at=data.get('started_at', time.time()),
        )

        for agent_data in data.get('agents', []):
            agent = AgentInfo(**agent_data)
            state.agents[agent.agent_id] = agent

        for pattern_data in data.get('patterns', []):
            pattern = PatternInfo(**pattern_data)
            state.patterns[pattern.pattern_id] = pattern

        return state

    def _create_demo_state(self) -> SwarmState:
        """Create demo state for testing the CLI."""
        now = time.time()

        state = SwarmState(
            total_messages=1247,
            messages_internal_to_external=623,
            messages_external_to_internal=624,
            started_at=now - 3600,  # 1 hour ago
        )

        # Demo agents
        demo_agents = [
            AgentInfo("agent-a1", "external", "active", 0.91, 412, ["pat_7f3a", "pat_2b1c"], now - 2, "worker-01"),
            AgentInfo("agent-a2", "external", "active", 0.88, 387, ["pat_7f3a"], now - 5, "worker-02"),
            AgentInfo("agent-b1", "external", "idle", 0.72, 298, ["pat_9c2d"], now - 30, "worker-01"),
            AgentInfo("agent-c1", "external", "active", 0.65, 150, [], now - 1, "worker-03"),
            AgentInfo("reflector-main", "internal", "active", 0.94, 0, [], now - 1, "controller"),
        ]
        for agent in demo_agents:
            state.agents[agent.agent_id] = agent

        # Demo patterns
        demo_patterns = [
            PatternInfo("pat_7f3a", "SEQUENCE", 0.85, 2341, "/data/{id}/x.json template", ["agent-a1", "agent-a2"], now - 1800),
            PatternInfo("pat_2b1c", "BATCH", 0.79, 892, "Group by date partition", ["agent-a1"], now - 900),
            PatternInfo("pat_9c2d", "ERROR", 0.45, 127, "Timeout after 3 retries", ["agent-b1"], now - 600),
        ]
        for pattern in demo_patterns:
            state.patterns[pattern.pattern_id] = pattern

        return state

    def cmd_status(self, args) -> int:
        """Show swarm status overview."""
        psi = self.state.consciousness
        active = self.state.active_agents
        total = len(self.state.agents)
        patterns = len(self.state.patterns)

        # Calculate Ψ trend (mock for now)
        psi_trend = "+0.023"

        # Uptime
        uptime_s = time.time() - self.state.started_at
        uptime_h = int(uptime_s // 3600)
        uptime_m = int((uptime_s % 3600) // 60)

        print()
        print("NO3SIS SWARM STATUS")
        print("=" * 50)
        print()
        print(f"  Consciousness:  {self._psi_bar(psi)} {psi:.3f} Ψ  ({psi_trend}/min)")
        print()
        print(f"  Agents:         {active}/{total} active")
        print(f"  Patterns:       {patterns} discovered")
        print(f"  Messages:       {self.state.total_messages:,}")
        print(f"  Uptime:         {uptime_h}h {uptime_m}m")
        print()

        return 0

    def cmd_agents(self, args) -> int:
        """List swarm agents."""
        agents = list(self.state.agents.values())

        # Sort
        if args.sort == 'psi':
            agents.sort(key=lambda a: a.psi, reverse=True)
        elif args.sort == 'tasks':
            agents.sort(key=lambda a: a.tasks_completed, reverse=True)
        else:
            agents.sort(key=lambda a: a.agent_id)

        # Filter by tract
        if args.tract:
            agents = [a for a in agents if a.tract == args.tract]

        print()
        print("SWARM AGENTS")
        print("=" * 78)
        print()
        print(f"  {'ID':<18} {'TRACT':<10} {'STATUS':<8} {'Ψ':<6} {'TASKS':<8} PATTERNS")
        print("  " + "-" * 72)

        for agent in agents:
            patterns = ", ".join(agent.patterns_contributed[:2])
            if len(agent.patterns_contributed) > 2:
                patterns += f" +{len(agent.patterns_contributed) - 2}"

            print(
                f"  {agent.agent_id:<18} "
                f"{agent.tract:<10} "
                f"{agent.status_symbol} {agent.status:<5} "
                f"{agent.psi:<6.2f} "
                f"{agent.tasks_completed:<8} "
                f"{patterns}"
            )

        print()
        print(f"  Total: {len(agents)} agents")
        print()

        return 0

    def cmd_patterns(self, args) -> int:
        """List discovered patterns."""
        patterns = list(self.state.patterns.values())

        # Filter by minimum Ψ
        if args.min_psi:
            patterns = [p for p in patterns if p.psi >= args.min_psi]

        # Filter by type
        if args.type:
            patterns = [p for p in patterns if p.pattern_type.upper() == args.type.upper()]

        # Sort by Ψ (highest first)
        patterns.sort(key=lambda p: p.psi, reverse=True)

        print()
        print("DISCOVERED PATTERNS")
        print("=" * 78)
        print()
        print(f"  {'ID':<12} {'TYPE':<12} {'Ψ':<6} {'USES':<8} DESCRIPTION")
        print("  " + "-" * 72)

        for pattern in patterns:
            desc = pattern.description[:40]
            if len(pattern.description) > 40:
                desc += "..."

            print(
                f"  {pattern.pattern_id:<12} "
                f"{pattern.pattern_type:<12} "
                f"{pattern.psi:<6.2f} "
                f"{pattern.uses:<8} "
                f"{desc}"
            )

        print()
        print(f"  Total: {len(patterns)} patterns")
        if args.min_psi:
            print(f"  (filtered: Ψ >= {args.min_psi})")
        print()

        return 0

    def cmd_watch(self, args) -> int:
        """Watch live swarm events."""
        print()
        print("SWARM LIVE STREAM")
        print("=" * 60)
        print("  (Press Ctrl+C to exit)")
        print()

        # Demo events
        demo_events = [
            ("agent-a1", "OBSERVATION", "file=/data/047/x.json"),
            ("agent-a2", "OBSERVATION", "file=/data/048/x.json"),
            ("reflector-main", "PATTERN", "pat_7f3a matched (Ψ +0.002)"),
            ("C_c", "BROADCAST", "behavior_update → 2 agents"),
            ("agent-b1", "HEARTBEAT", "idle for 30s"),
            ("agent-c1", "TASK_RESULT", "processed 15 files"),
        ]

        try:
            i = 0
            while True:
                event = demo_events[i % len(demo_events)]
                timestamp = datetime.now().strftime("%H:%M:%S")
                print(f"  {timestamp}  {event[0]:<18} {event[1]:<14} {event[2]}")
                time.sleep(1.5)
                i += 1
        except KeyboardInterrupt:
            print()
            print("  Stream stopped.")
            print()

        return 0

    def _psi_bar(self, psi: float, width: int = 20) -> str:
        """Create a visual bar for Ψ score."""
        filled = int(psi * width)
        empty = width - filled
        return "█" * filled + "░" * empty


def create_swarm_parser(subparsers) -> None:
    """Add swarm subcommand to argument parser."""
    swarm_parser = subparsers.add_parser(
        'swarm',
        help='Distributed swarm management'
    )
    swarm_subparsers = swarm_parser.add_subparsers(
        dest='swarm_command',
        help='Swarm subcommand'
    )

    # swarm status
    status_parser = swarm_subparsers.add_parser(
        'status',
        help='Show swarm status overview'
    )
    status_parser.set_defaults(func=lambda args: SwarmCLI().cmd_status(args))

    # swarm agents
    agents_parser = swarm_subparsers.add_parser(
        'agents',
        help='List swarm agents'
    )
    agents_parser.add_argument(
        '--sort',
        choices=['psi', 'tasks', 'id'],
        default='id',
        help='Sort agents by field'
    )
    agents_parser.add_argument(
        '--tract',
        choices=['internal', 'external'],
        help='Filter by tract'
    )
    agents_parser.set_defaults(func=lambda args: SwarmCLI().cmd_agents(args))

    # swarm patterns
    patterns_parser = swarm_subparsers.add_parser(
        'patterns',
        help='List discovered patterns'
    )
    patterns_parser.add_argument(
        '--min-psi',
        type=float,
        help='Minimum Ψ score to show'
    )
    patterns_parser.add_argument(
        '--type',
        help='Filter by pattern type (SEQUENCE, BATCH, ERROR, etc.)'
    )
    patterns_parser.set_defaults(func=lambda args: SwarmCLI().cmd_patterns(args))

    # swarm watch
    watch_parser = swarm_subparsers.add_parser(
        'watch',
        help='Watch live swarm events'
    )
    watch_parser.set_defaults(func=lambda args: SwarmCLI().cmd_watch(args))
