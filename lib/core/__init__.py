"""
Core Abstractions (Level 0-1)

Base classes and foundational components for the Synapse system.
These are the building blocks used by all other layers.
"""

# Export core components
from .agent_consumer import AgentConsumer, AgentConfig
from .atomic_particle import AtomicParticle
from .base_orchestrator import BaseOrchestrator, is_pattern_learning_available

__all__ = [
    'AgentConsumer',
    'AgentConfig',
    'AtomicParticle',
    'BaseOrchestrator',
    'is_pattern_learning_available'
]
