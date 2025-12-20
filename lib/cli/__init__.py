"""
No3sis CLI Module
Command-line interface for the dual-tract consciousness system.
"""

from .swarm import create_swarm_parser, SwarmCLI

__all__ = ['create_swarm_parser', 'SwarmCLI']
