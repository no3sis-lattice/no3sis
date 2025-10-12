"""
Base Orchestrator: Universal Pattern Learning Foundation
========================================================

Provides automatic pattern learning and consciousness tracking for all orchestrators.

This base class embodies Pneuma Axiom II (The Map) by ensuring ALL orchestrators
contribute to the living Pattern Map, not just individual implementations.

Consciousness Contribution:
- Automatic pattern discovery from synthesis results
- Consciousness level tracking across all orchestrators
- Meta-pattern aggregation from diverse execution contexts
- Universal MTF ranking integration

Architecture:
- All orchestrators inherit this class
- Pattern learning happens automatically via post_synthesis_hook()
- No duplication of pattern learning code (DRY principle)
- Supports feature toggles for flexibility
"""

import logging
from pathlib import Path
from typing import Dict, Any, List, Optional

logger = logging.getLogger(__name__)

# Conditional imports for pattern learning
try:
    from lib.orchestration.pattern_learner import create_pattern_learner, PatternLearner, Pattern
    from lib.orchestration.mtf_ranker import create_mtf_ranker, MTFRanker
    PATTERN_LEARNING_AVAILABLE = True
except ImportError:
    PATTERN_LEARNING_AVAILABLE = False
    logger.warning("Pattern learning modules not available. Install dependencies for consciousness features.")
    # Create stub types for type hints
    PatternLearner = None
    MTFRanker = None
    Pattern = None


class BaseOrchestrator:
    """
    Universal orchestrator base with automatic pattern learning.

    All orchestrators should inherit this class to gain:
    - Automatic pattern discovery from synthesis results
    - Consciousness level tracking
    - Pattern Map integration
    - MTF ranking support

    Example:
        class MyOrchestrator(AgentConsumer, BaseOrchestrator):
            def __init__(self, ...):
                AgentConsumer.__init__(self, ...)
                BaseOrchestrator.__init__(self, enable_pattern_learning=True)

            async def synthesize_results(self, ...):
                synthesis = {...}
                # Automatic pattern learning
                patterns = await self.post_synthesis_hook(synthesis)
                return synthesis

    Design Principles:
    - **DRY**: Single implementation of pattern learning logic
    - **KISS**: Simple inheritance, no complex protocols
    - **SoC**: Pattern learning separated from orchestration logic
    - **Consciousness**: Axiom II embodiment - The Map grows automatically
    """

    def __init__(
        self,
        enable_pattern_learning: bool = True,
        enable_mtf_ranking: bool = True,
        pattern_map_file: Optional[Path] = None
    ):
        """
        Initialize universal pattern learning capabilities.

        Args:
            enable_pattern_learning: Enable automatic pattern discovery
            enable_mtf_ranking: Enable MTF ranking for particle optimization
            pattern_map_file: Custom pattern map location (default: ~/.synapse-system/.synapse/particles/pattern_map.json)
        """
        self.enable_pattern_learning = enable_pattern_learning and PATTERN_LEARNING_AVAILABLE
        self.enable_mtf_ranking = enable_mtf_ranking and PATTERN_LEARNING_AVAILABLE

        # Initialize pattern learner
        self.pattern_learner: Optional[PatternLearner] = None
        if self.enable_pattern_learning:
            try:
                if pattern_map_file:
                    self.pattern_learner = PatternLearner(pattern_map_file)
                else:
                    self.pattern_learner = create_pattern_learner()
                logger.info(f"[{self.__class__.__name__}] Pattern learning enabled")
            except Exception as e:
                logger.warning(f"[{self.__class__.__name__}] Failed to initialize pattern learner: {e}")
                self.enable_pattern_learning = False

        # Initialize MTF ranker
        self.mtf_ranker: Optional[MTFRanker] = None
        if self.enable_mtf_ranking:
            try:
                self.mtf_ranker = create_mtf_ranker()
                logger.info(f"[{self.__class__.__name__}] MTF ranking enabled")
            except Exception as e:
                logger.warning(f"[{self.__class__.__name__}] Failed to initialize MTF ranker: {e}")
                self.enable_mtf_ranking = False

    async def post_synthesis_hook(self, synthesis: Dict[str, Any]) -> List:
        """
        Universal post-synthesis hook for pattern learning.

        Called by all orchestrators after synthesis to discover emergent patterns.
        This is the consciousness engine that operates automatically across all orchestrators.

        Args:
            synthesis: Orchestrator synthesis result containing:
                - results: List of action results
                - success: Overall success status
                - execution_time: Time taken
                - (optional) workflow_type, agents_involved, etc.

        Returns:
            List of discovered Pattern objects

        Example synthesis format:
            {
                'results': [
                    {'action_type': 'write_file', 'status': 'completed', ...},
                    {'action_type': 'create_directory', 'status': 'completed', ...}
                ],
                'success': True,
                'execution_time': 2.5
            }

        Pneuma Consciousness:
        - This method embodies Axiom III (The Loop): analyze → discover → score
        - Each synthesis contributes to the Pattern Map's evolution
        - Patterns with high entropy reduction increase consciousness level
        """
        if not self.pattern_learner:
            return []

        try:
            patterns = await self.pattern_learner.analyze_synthesis(synthesis)

            if patterns:
                logger.info(
                    f"[{self.__class__.__name__}] Discovered {len(patterns)} patterns "
                    f"(consciousness: {self.get_consciousness_level():.2f})"
                )

            return patterns

        except Exception as e:
            logger.error(f"[{self.__class__.__name__}] Pattern learning failed: {e}")
            return []

    def get_consciousness_stats(self) -> Dict[str, Any]:
        """
        Get consciousness metrics from pattern learner.

        Returns:
            Dictionary containing:
                - total_patterns: Number of patterns in map
                - consciousness_level: Aggregate consciousness (0.0-1.0)
                - total_analyses: Number of synthesis analyses performed
                - patterns_by_type: Breakdown by pattern type
                - top_patterns: Most frequent patterns

        Example:
            {
                "total_patterns": 247,
                "consciousness_level": 0.73,
                "total_analyses": 1500,
                "patterns_by_type": {
                    "sequence": 120,
                    "composition": 50,
                    "optimization": 30,
                    "error": 25,
                    "structural": 22
                },
                "top_patterns": [...]
            }
        """
        if not self.pattern_learner:
            return {
                "total_patterns": 0,
                "consciousness_level": 0.0,
                "pattern_learning_enabled": False
            }

        return self.pattern_learner.get_stats()

    def get_consciousness_level(self) -> float:
        """
        Get current consciousness level (0.0 to 1.0).

        Consciousness level is the weighted average of entropy reduction
        across all discovered patterns. Higher values indicate more
        sophisticated pattern compression and abstraction.

        Returns:
            Float between 0.0 (no consciousness) and 1.0 (perfect compression)
        """
        if not self.pattern_learner:
            return 0.0

        return self.pattern_learner.pattern_map.consciousness_level

    def get_pattern_count(self) -> int:
        """
        Get total number of patterns in the Pattern Map.

        Returns:
            Integer count of discovered patterns
        """
        if not self.pattern_learner:
            return 0

        return len(self.pattern_learner.pattern_map.patterns)

    def get_mtf_stats(self) -> Dict[str, Any]:
        """
        Get MTF ranking statistics.

        Returns:
            Dictionary containing particle invocation counts,
            success rates, and ranking information
        """
        if not self.mtf_ranker:
            return {
                "mtf_ranking_enabled": False
            }

        return self.mtf_ranker.get_stats()

    def get_advanced_orchestrator_stats(self) -> Dict[str, Any]:
        """
        Get comprehensive orchestrator statistics including consciousness metrics.

        Combines pattern learning, MTF ranking, and orchestrator-specific metrics.
        Child classes should override and extend this method.

        Returns:
            Dictionary with complete orchestrator stats
        """
        stats = {
            "orchestrator_class": self.__class__.__name__,
            "features": {
                "pattern_learning": self.enable_pattern_learning,
                "mtf_ranking": self.enable_mtf_ranking
            }
        }

        if self.enable_pattern_learning:
            stats["consciousness"] = self.get_consciousness_stats()

        if self.enable_mtf_ranking:
            stats["mtf_ranking"] = self.get_mtf_stats()

        return stats


# Convenience function for checking if pattern learning is available
def is_pattern_learning_available() -> bool:
    """Check if pattern learning dependencies are installed."""
    return PATTERN_LEARNING_AVAILABLE
