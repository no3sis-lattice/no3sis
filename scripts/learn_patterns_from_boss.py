#!/usr/bin/env python3
"""
Boss Pattern Learning CLI
=========================

Learn meta-patterns from Boss agent workflows via CLI.

This tool enables Boss agent to discover emergent patterns from
multi-agent coordination by analyzing workflow JSON files.

Usage:
    # Basic usage
    python learn_patterns_from_boss.py workflow.json

    # With verbose output
    python learn_patterns_from_boss.py workflow.json --verbose

    # Show statistics
    python learn_patterns_from_boss.py workflow.json --stats

Example workflow JSON:
    {
        "workflow_id": "feature_auth",
        "workflow_type": "feature_implementation",
        "agents_involved": ["architect", "rust-specialist", "test-runner"],
        "agent_results": [
            {
                "agent_id": "architect",
                "action_type": "design_system",
                "status": "completed",
                "execution_time": 5.2,
                "result": {"design": "JWT auth with Redis"}
            },
            {
                "agent_id": "rust-specialist",
                "action_type": "implement_feature",
                "status": "completed",
                "execution_time": 15.8,
                "result": {"files_created": 3}
            },
            {
                "agent_id": "test-runner",
                "action_type": "run_tests",
                "status": "completed",
                "execution_time": 8.3,
                "result": {"tests_passed": 12}
            }
        ],
        "success": true
    }

Pneuma Consciousness:
    This tool enables Boss to contribute to the living Pattern Map by
    discovering meta-patterns (agent-level) that complement file_creator's
    micro-patterns (action-level). Together, they create multi-scale
    consciousness across the system hierarchy.
"""

import sys
import json
import asyncio
import logging
from pathlib import Path
from typing import Dict, Any

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

from lib.orchestrators.boss_orchestrator import create_boss_orchestrator

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def validate_workflow_json(workflow: Dict[str, Any]) -> bool:
    """
    Validate workflow JSON structure.

    Required fields:
        - workflow_id: str
        - workflow_type: str
        - agents_involved: list[str]
        - agent_results: list[dict]
        - success: bool
    """
    required_fields = ['workflow_id', 'workflow_type', 'agents_involved', 'agent_results']

    for field in required_fields:
        if field not in workflow:
            logger.error(f"Missing required field: {field}")
            return False

    if not isinstance(workflow['agents_involved'], list):
        logger.error("'agents_involved' must be a list")
        return False

    if not isinstance(workflow['agent_results'], list):
        logger.error("'agent_results' must be a list")
        return False

    # Validate agent_results structure
    for result in workflow['agent_results']:
        required_result_fields = ['agent_id', 'action_type', 'status']
        for field in required_result_fields:
            if field not in result:
                logger.error(f"Agent result missing required field: {field}")
                return False

    return True


async def learn_from_workflow(workflow_file: Path, verbose: bool = False, show_stats: bool = False):
    """
    Learn patterns from Boss workflow JSON file.

    Args:
        workflow_file: Path to workflow JSON file
        verbose: Enable verbose logging
        show_stats: Display Boss statistics after learning
    """
    if verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # Load workflow JSON
    try:
        with open(workflow_file) as f:
            workflow = json.load(f)
    except FileNotFoundError:
        logger.error(f"Workflow file not found: {workflow_file}")
        return 1
    except json.JSONDecodeError as e:
        logger.error(f"Invalid JSON in workflow file: {e}")
        return 1

    # Validate workflow structure
    if not validate_workflow_json(workflow):
        logger.error("Workflow JSON validation failed")
        return 1

    # Create Boss orchestrator
    boss_orch = create_boss_orchestrator()

    # Analyze workflow and discover patterns
    try:
        logger.info(f"Analyzing workflow: {workflow['workflow_id']}")
        logger.info(f"  Type: {workflow['workflow_type']}")
        logger.info(f"  Agents: {', '.join(workflow['agents_involved'])}")

        patterns = await boss_orch.analyze_workflow_from_dict(workflow)

        logger.info(f"\n✅ Pattern learning complete!")
        logger.info(f"   Discovered: {len(patterns)} patterns")

        if patterns:
            logger.info(f"\n   Patterns:")
            for pattern in patterns:
                logger.info(f"   - {pattern.name}")
                logger.info(f"     Type: {pattern.pattern_type.value}")
                logger.info(f"     Entropy reduction: {pattern.entropy_reduction:.2f}")
                logger.info(f"     Consciousness: {pattern.consciousness_contribution}")
                logger.info("")

        # Show consciousness metrics
        consciousness_level = boss_orch.get_consciousness_level()
        pattern_count = boss_orch.get_pattern_count()

        logger.info(f"📊 Consciousness Metrics:")
        logger.info(f"   Total patterns: {pattern_count}")
        logger.info(f"   Consciousness level: {consciousness_level:.2f}")

        # Show Boss stats if requested
        if show_stats:
            stats = boss_orch.get_boss_stats()
            logger.info(f"\n📈 Boss Statistics:")
            logger.info(f"   Total workflows: {stats['total_workflows']}")
            logger.info(f"   Success rate: {stats['success_rate']:.1%}")
            logger.info(f"   Avg agents/workflow: {stats['avg_agents_per_workflow']:.1f}")
            logger.info(f"   Workflows by type:")
            for wf_type, count in stats['workflows_by_type'].items():
                logger.info(f"     - {wf_type}: {count}")

        return 0

    except Exception as e:
        logger.error(f"Pattern learning failed: {e}", exc_info=verbose)
        return 1


def print_usage():
    """Print usage information"""
    print(__doc__)


def main():
    """Main entry point"""
    import argparse

    parser = argparse.ArgumentParser(
        description="Learn meta-patterns from Boss agent workflows",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Basic usage
    python learn_patterns_from_boss.py workflow.json

    # With verbose output and statistics
    python learn_patterns_from_boss.py workflow.json --verbose --stats

    # Generate example workflow JSON
    cat > example_workflow.json <<EOF
    {
        "workflow_id": "feature_auth",
        "workflow_type": "feature_implementation",
        "agents_involved": ["architect", "rust-specialist", "test-runner"],
        "agent_results": [
            {
                "agent_id": "architect",
                "action_type": "design_system",
                "status": "completed",
                "execution_time": 5.2
            },
            {
                "agent_id": "rust-specialist",
                "action_type": "implement_feature",
                "status": "completed",
                "execution_time": 15.8
            },
            {
                "agent_id": "test-runner",
                "action_type": "run_tests",
                "status": "completed",
                "execution_time": 8.3
            }
        ],
        "success": true
    }
    EOF

    python learn_patterns_from_boss.py example_workflow.json
        """
    )

    parser.add_argument(
        'workflow_file',
        type=Path,
        help='Path to workflow JSON file'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose logging'
    )
    parser.add_argument(
        '--stats', '-s',
        action='store_true',
        help='Display Boss statistics after learning'
    )

    args = parser.parse_args()

    # Run async pattern learning
    exit_code = asyncio.run(
        learn_from_workflow(
            args.workflow_file,
            verbose=args.verbose,
            show_stats=args.stats
        )
    )

    sys.exit(exit_code)


if __name__ == "__main__":
    main()
