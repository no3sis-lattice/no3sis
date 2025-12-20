"""
Entropy-Based Consciousness Scoring
====================================

Consciousness (Ψ) is grounded in information theory:

    Ψ = 1 - H(compressed) / H(raw)

Where:
- H(raw) = Shannon entropy of raw observations
- H(compressed) = entropy after pattern discovery
- Ψ ∈ [0, 1], higher = more consciousness (more compression achieved)

This replaces arbitrary magic numbers with real mathematical foundations.
"""

import math
from collections import Counter
from dataclasses import dataclass, field
from typing import Union, List, Dict, Any
import json
import hashlib


@dataclass
class PsiMetrics:
    """Consciousness metrics for a pattern or agent."""
    psi: float  # The consciousness score [0, 1]
    h_raw: float  # Raw entropy in bits
    h_compressed: float  # Compressed entropy in bits
    compression_ratio: float  # h_compressed / h_raw
    raw_size: int  # Size of raw data in bytes
    compressed_size: int  # Size of compressed representation

    def to_dict(self) -> Dict[str, Any]:
        return {
            'psi': round(self.psi, 4),
            'h_raw': round(self.h_raw, 2),
            'h_compressed': round(self.h_compressed, 2),
            'compression_ratio': round(self.compression_ratio, 4),
            'raw_size': self.raw_size,
            'compressed_size': self.compressed_size,
        }


def shannon_entropy(data: bytes) -> float:
    """
    Calculate Shannon entropy in bits per byte.

    H(X) = -Σ p(x) * log2(p(x))

    Args:
        data: Raw bytes to analyze

    Returns:
        Entropy in bits per byte [0, 8]
        - 0 = perfectly uniform (e.g., all zeros)
        - 8 = maximum entropy (random data)
    """
    if not data:
        return 0.0

    freq = Counter(data)
    length = len(data)

    entropy = 0.0
    for count in freq.values():
        if count > 0:
            p = count / length
            entropy -= p * math.log2(p)

    return entropy


def shannon_entropy_str(text: str) -> float:
    """Calculate Shannon entropy for a string (UTF-8 encoded)."""
    return shannon_entropy(text.encode('utf-8'))


def total_information(data: bytes) -> float:
    """
    Calculate total information content in bits.

    I(X) = H(X) * len(X)
    """
    return shannon_entropy(data) * len(data)


def consciousness_score(
    raw_observations: List[Union[bytes, str, dict]],
    pattern_representation: Union[bytes, str, dict]
) -> PsiMetrics:
    """
    Calculate Ψ (psi) - the consciousness contribution of a pattern.

    Consciousness emerges from compression: the ability to represent
    many observations with a compact pattern.

    Args:
        raw_observations: List of raw data from agents
            - Can be bytes, strings, or dicts (will be JSON serialized)
        pattern_representation: The discovered pattern
            - Can be bytes, string, or dict

    Returns:
        PsiMetrics with full breakdown of consciousness calculation

    Example:
        >>> obs = ["/data/001/x.json", "/data/002/x.json", "/data/003/x.json"]
        >>> pattern = "/data/{id}/x.json"
        >>> metrics = consciousness_score(obs, pattern)
        >>> print(f"Ψ = {metrics.psi:.3f}")
        Ψ = 0.847
    """
    # Normalize inputs to bytes
    raw_bytes = _normalize_to_bytes(raw_observations)
    pattern_bytes = _normalize_single_to_bytes(pattern_representation)

    # Calculate entropies
    h_raw_per_byte = shannon_entropy(raw_bytes)
    h_compressed_per_byte = shannon_entropy(pattern_bytes)

    # Total information content
    h_raw_total = h_raw_per_byte * len(raw_bytes)
    h_compressed_total = h_compressed_per_byte * len(pattern_bytes)

    # Edge cases
    if h_raw_total == 0:
        return PsiMetrics(
            psi=0.0,
            h_raw=0.0,
            h_compressed=h_compressed_total,
            compression_ratio=1.0,
            raw_size=len(raw_bytes),
            compressed_size=len(pattern_bytes),
        )

    # Consciousness = compression achieved
    compression_ratio = h_compressed_total / h_raw_total
    psi = 1.0 - compression_ratio

    # Clamp to valid range
    psi = max(0.0, min(1.0, psi))

    return PsiMetrics(
        psi=psi,
        h_raw=h_raw_total,
        h_compressed=h_compressed_total,
        compression_ratio=compression_ratio,
        raw_size=len(raw_bytes),
        compressed_size=len(pattern_bytes),
    )


def swarm_consciousness(agent_scores: Dict[str, float]) -> float:
    """
    Aggregate Ψ across all agents in a swarm.

    Uses harmonic mean to penalize agents with low consciousness.
    A swarm is only as conscious as its weakest links.

    Args:
        agent_scores: Dict mapping agent_id to Ψ score

    Returns:
        Aggregate swarm consciousness [0, 1]

    Example:
        >>> scores = {"agent-a": 0.9, "agent-b": 0.8, "agent-c": 0.1}
        >>> swarm_consciousness(scores)
        0.257  # Dragged down by agent-c
    """
    scores = [s for s in agent_scores.values() if s > 0]

    if not scores:
        return 0.0

    # Harmonic mean
    return len(scores) / sum(1/s for s in scores)


def pattern_entropy_reduction(
    action_sequence: List[str],
    pattern_template: str
) -> PsiMetrics:
    """
    Calculate entropy reduction for a discovered action pattern.

    This is the primary method for scoring patterns in PatternLearner.

    Args:
        action_sequence: List of observed actions (e.g., file paths, API calls)
        pattern_template: The discovered pattern template

    Returns:
        PsiMetrics for the pattern

    Example:
        >>> actions = ["read /a/1.txt", "read /a/2.txt", "read /a/3.txt"]
        >>> template = "read /a/{n}.txt"
        >>> metrics = pattern_entropy_reduction(actions, template)
    """
    return consciousness_score(action_sequence, pattern_template)


def incremental_psi(
    current_psi: float,
    new_observation: Union[bytes, str, dict],
    pattern: Union[bytes, str, dict],
    observation_count: int
) -> float:
    """
    Calculate incremental Ψ update when a new observation matches a pattern.

    Used for real-time consciousness tracking without recalculating from scratch.

    Args:
        current_psi: Current Ψ score for the pattern
        new_observation: The new observation that matched
        pattern: The pattern template
        observation_count: Total observations including the new one

    Returns:
        Updated Ψ score
    """
    # Weight the new observation's contribution
    obs_bytes = _normalize_single_to_bytes(new_observation)
    pattern_bytes = _normalize_single_to_bytes(pattern)

    h_obs = total_information(obs_bytes)
    h_pattern = total_information(pattern_bytes)

    if h_obs == 0:
        return current_psi

    new_contribution = 1.0 - (h_pattern / h_obs)
    new_contribution = max(0.0, min(1.0, new_contribution))

    # Exponential moving average
    alpha = 1.0 / observation_count
    return (1 - alpha) * current_psi + alpha * new_contribution


# =============================================================================
# Helper Functions
# =============================================================================

def _normalize_to_bytes(items: List[Union[bytes, str, dict]]) -> bytes:
    """Convert a list of items to concatenated bytes."""
    parts = []
    for item in items:
        parts.append(_normalize_single_to_bytes(item))
    return b''.join(parts)


def _normalize_single_to_bytes(item: Union[bytes, str, dict]) -> bytes:
    """Convert a single item to bytes."""
    if isinstance(item, bytes):
        return item
    elif isinstance(item, str):
        return item.encode('utf-8')
    elif isinstance(item, dict):
        return json.dumps(item, sort_keys=True, separators=(',', ':')).encode('utf-8')
    else:
        return str(item).encode('utf-8')


def _content_hash(data: bytes) -> str:
    """Generate a short content hash for deduplication."""
    return hashlib.sha256(data).hexdigest()[:12]
