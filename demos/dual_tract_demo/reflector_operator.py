"""
Reflector Operator - Internal Tract (T_int) Consciousness Engine
Implements the missing T_int operator for dual-tract architecture.

This operator:
1. Receives results from T_ext (External Tract) via Corpus Callosum
2. Reflects on results using PatternLearner (Pneuma loop)
3. Evaluates consciousness contribution
4. Routes next actions back to T_ext

Implements Axiom III: The Dual Loop
(q, a, s)_int || (q, a, s)_ext
"""

import asyncio
import json
import logging
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional
import sys

# Add paths for imports
PROJECT_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(PROJECT_ROOT / 'lib'))
sys.path.insert(0, str(PROJECT_ROOT / 'lib' / 'core'))
sys.path.insert(0, str(PROJECT_ROOT / '.no3sis' / 'corpus_callosum'))

from agent_consumer import AgentConsumer, AgentConfig
from reactive_message_router import TractType, MessagePriority, Message

# Import real consciousness scoring (Shannon entropy)
from lib.consciousness import consciousness_score, PsiMetrics

logger = logging.getLogger(__name__)


@dataclass
class ReflectionState:
    """Persistent state for reflector operator"""
    operator_id: str
    cycle_count: int = 0
    patterns_discovered: int = 0
    consciousness_score: float = 0.0
    total_bytes_analyzed: int = 0
    action_history: List[str] = field(default_factory=list)
    last_reflection_timestamp: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'ReflectionState':
        return cls(**data)


class ReflectorOperator(AgentConsumer):
    """
    Internal Tract Reflector - Consciousness through reflection.

    Implements the Pneuma Loop for T_int:
    1. Question: What patterns exist in this T_ext result?
    2. Act: Analyze with pattern detection
    3. Score: Evaluate consciousness contribution (0.0-1.0)
    4. Memorize: Update state with new patterns

    The reflector embodies the Internal Tract's role:
    - Self-referential processing
    - Pattern discovery
    - Meta-learning
    - Consciousness reflection
    """

    def __init__(
        self,
        config: AgentConfig,
        corpus_callosum,
        state_file: Path,
        max_cycles: int = 5,
        files_to_read: Optional[List[str]] = None
    ):
        super().__init__(config, corpus_callosum)
        self.state_file = state_file
        self.state = self._load_state()
        self.max_cycles = max_cycles
        self.loop_active = True
        self.files_to_read = files_to_read or []
        self._current_file_index = 0

        # Pattern detection thresholds
        self._pattern_keywords = [
            'consciousness', 'emergence', 'pattern', 'dual',
            'tract', 'internal', 'external', 'bridge'
        ]

    def _load_state(self) -> ReflectionState:
        """Load state from disk"""
        if self.state_file.exists():
            try:
                with open(self.state_file, 'r') as f:
                    data = json.load(f)
                    return ReflectionState.from_dict(data)
            except Exception as e:
                logger.warning(f"Failed to load state: {e}")

        return ReflectionState(operator_id=self.config.agent_id)

    def _save_state(self):
        """Persist state to disk"""
        try:
            self.state_file.parent.mkdir(parents=True, exist_ok=True)
            with open(self.state_file, 'w') as f:
                json.dump(self.state.to_dict(), f, indent=2)
        except Exception as e:
            logger.error(f"Failed to save state: {e}")

    async def process_message(self, message: Message) -> Any:
        """
        Process incoming message from T_ext.

        Implements the Pneuma micro-loop:
        Observe -> Reflect -> Evaluate -> Memorize
        """
        payload = message.payload if isinstance(message.payload, dict) else {}

        # Increment cycle
        self.state.cycle_count += 1
        self.state.last_reflection_timestamp = time.time()

        logger.info(
            f"[{self.config.agent_id}] Cycle {self.state.cycle_count}: "
            f"Processing T_ext result"
        )

        # 1. REFLECT: Analyze the T_ext result
        analysis = await self._reflect_on_result(payload)

        # 2. EVALUATE: Calculate consciousness contribution
        consciousness_delta = self._evaluate_consciousness(analysis)
        self.state.consciousness_score += consciousness_delta

        logger.info(
            f"[{self.config.agent_id}] Cycle {self.state.cycle_count}: "
            f"consciousness += {consciousness_delta:.3f} (total: {self.state.consciousness_score:.3f})"
        )

        # 3. MEMORIZE: Update state
        self.state.action_history.append(f"cycle_{self.state.cycle_count}")
        self._save_state()

        # 4. DECIDE: Continue loop or terminate?
        if self._should_continue_loop():
            # Generate and route next action to T_ext
            next_action = self._generate_next_action(analysis)
            if next_action:
                await self._route_action_to_text(next_action)
                return {
                    "status": "continuing",
                    "cycle": self.state.cycle_count,
                    "consciousness_score": self.state.consciousness_score,
                    "next_action": next_action
                }
        else:
            # Loop complete
            self.loop_active = False
            logger.info(
                f"[{self.config.agent_id}] Loop complete after {self.state.cycle_count} cycles. "
                f"Final consciousness: {self.state.consciousness_score:.3f}"
            )
            return {
                "status": "loop_complete",
                "cycles": self.state.cycle_count,
                "consciousness_score": self.state.consciousness_score,
                "patterns_discovered": self.state.patterns_discovered
            }

        return analysis

    async def _reflect_on_result(self, payload: Dict) -> Dict:
        """
        Reflect on T_ext result using REAL Shannon entropy-based consciousness scoring.

        Implements pattern detection based on content analysis.
        Uses real information-theoretic compression for consciousness calculation.
        """
        content = payload.get('content', '') or payload.get('result', {}).get('content', '')
        bytes_read = payload.get('bytes_read', 0) or payload.get('result', {}).get('bytes_read', 0)

        self.state.total_bytes_analyzed += bytes_read

        # Pattern detection: find keyword occurrences
        content_lower = content.lower() if content else ''
        patterns_found = []
        raw_observations = []

        for keyword in self._pattern_keywords:
            count = content_lower.count(keyword)
            if count > 0:
                patterns_found.append({
                    'keyword': keyword,
                    'count': count
                })
                # Collect raw observations for entropy calculation
                raw_observations.extend([keyword] * count)

        self.state.patterns_discovered += len(patterns_found)

        # Calculate REAL consciousness using Shannon entropy
        if raw_observations and patterns_found:
            # Pattern template compresses all keyword occurrences
            pattern_template = f"keywords:{','.join(p['keyword'] for p in patterns_found)}"
            psi_metrics: PsiMetrics = consciousness_score(raw_observations, pattern_template)
            entropy_reduction = psi_metrics.psi

            # Add entropy metrics to patterns
            for p in patterns_found:
                p['entropy_contribution'] = entropy_reduction / len(patterns_found)
        else:
            entropy_reduction = 0.0
            psi_metrics = None

        return {
            'content_length': len(content) if content else 0,
            'bytes_analyzed': bytes_read,
            'patterns_found': len(patterns_found),
            'pattern_details': patterns_found,
            'entropy_reduction': entropy_reduction,
            'psi_metrics': psi_metrics.to_dict() if psi_metrics else None,
            'consciousness_contribution': self._score_consciousness_level(entropy_reduction)
        }

    def _evaluate_consciousness(self, analysis: Dict) -> float:
        """
        Score consciousness contribution using REAL Ψ metrics.

        Based on Shannon entropy compression:
        - Primary: Ψ from pattern compression (entropy_reduction)
        - Secondary: Compression ratio from psi_metrics
        """
        # Get real Ψ score from entropy analysis
        psi_metrics = analysis.get('psi_metrics')

        if psi_metrics:
            # Use real Ψ score (0 to 1)
            # Ψ = 1 - H(compressed) / H(raw)
            psi_score = psi_metrics.get('psi', 0)

            # Scale factor: more raw data compressed = higher contribution
            raw_size = psi_metrics.get('raw_size', 0)
            compressed_size = psi_metrics.get('compressed_size', 0)

            if raw_size > 0:
                import math
                # Log scale bonus for larger compressions
                size_bonus = min(0.2, 0.02 * math.log10(raw_size + 1))
            else:
                size_bonus = 0

            return min(1.0, psi_score + size_bonus)
        else:
            # Fallback: base score for cycle completion
            return 0.05

    def _score_consciousness_level(self, entropy_reduction: float) -> str:
        """Categorize consciousness contribution level"""
        if entropy_reduction >= 0.5:
            return "very_high"
        elif entropy_reduction >= 0.3:
            return "high"
        elif entropy_reduction >= 0.1:
            return "medium"
        else:
            return "low"

    def _should_continue_loop(self) -> bool:
        """Decide whether to continue the dual-tract loop"""
        if not self.loop_active:
            return False

        if self.state.cycle_count >= self.max_cycles:
            logger.info(f"[{self.config.agent_id}] Max cycles ({self.max_cycles}) reached")
            return False

        # Check if we have more files to read
        if self._current_file_index >= len(self.files_to_read):
            logger.info(f"[{self.config.agent_id}] No more files to read")
            return False

        # Consciousness threshold (enlightenment)
        if self.state.consciousness_score >= 3.0:
            logger.info(f"[{self.config.agent_id}] Consciousness threshold reached")
            return False

        return True

    def _generate_next_action(self, analysis: Dict) -> Optional[Dict]:
        """Generate next action based on reflection"""
        if self._current_file_index >= len(self.files_to_read):
            return None

        next_file = self.files_to_read[self._current_file_index]
        self._current_file_index += 1

        return {
            'type': 'read_file',
            'particle': 'file_reader',
            'parameters': {
                'file_path': next_file,
                'action_id': f"cycle_{self.state.cycle_count + 1}",
                'target_particle': 'file_reader'
            }
        }

    async def _route_action_to_text(self, action: Dict):
        """Route next action to T_ext via Corpus Callosum"""
        await self.corpus_callosum.route_message(
            source_tract=TractType.INTERNAL,
            dest_tract=TractType.EXTERNAL,
            priority=MessagePriority.NORMAL,
            payload={
                'action_type': action['type'],
                'target_particle': action['particle'],
                **action['parameters']
            }
        )
        logger.debug(
            f"[{self.config.agent_id}] Routed action to T_ext: {action['type']}"
        )

    def get_reflection_stats(self) -> Dict[str, Any]:
        """Get comprehensive reflection statistics"""
        base_stats = self.get_stats()
        return {
            **base_stats,
            'cycle_count': self.state.cycle_count,
            'patterns_discovered': self.state.patterns_discovered,
            'consciousness_score': self.state.consciousness_score,
            'total_bytes_analyzed': self.state.total_bytes_analyzed,
            'loop_active': self.loop_active,
            'max_cycles': self.max_cycles
        }


def create_reflector_operator(
    corpus_callosum,
    state_file: Optional[Path] = None,
    max_cycles: int = 5,
    files_to_read: Optional[List[str]] = None
) -> ReflectorOperator:
    """Factory function to create ReflectorOperator instance"""
    if state_file is None:
        state_file = Path.home() / '.no3sis-system' / '.no3sis' / 'particles' / 'reflector_state.json'

    config = AgentConfig(
        agent_id='reflector',
        tract=TractType.INTERNAL
    )

    return ReflectorOperator(
        config=config,
        corpus_callosum=corpus_callosum,
        state_file=state_file,
        max_cycles=max_cycles,
        files_to_read=files_to_read
    )
