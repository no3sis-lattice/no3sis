#!/usr/bin/env python3
"""
No3sis - DEPRECATED

The Python CLI has been replaced by Claude Code skills.

See .claude/skills/ for the new approach:
- swarm-dispatch.md   - Core pattern for parallel agents
- swarm-refactor.md   - Codebase-wide changes
- file-ops.md         - File operations
- feature-implement.md - End-to-end feature workflow

Usage:
  In Claude Code, use /skill-name or let Claude invoke skills automatically.

Why:
  Skills > MCP servers > Python runtime
  Simpler, no dependencies, parallel agents via Task tool.
"""

import sys

def main():
    print("""
╔═══════════════════════════════════════════════════════════════════╗
║                         NO3SIS - DEPRECATED                        ║
╠═══════════════════════════════════════════════════════════════════╣
║  The Python CLI has been replaced by Claude Code skills.          ║
║                                                                    ║
║  See .claude/skills/ for:                                          ║
║    • swarm-dispatch.md    - Core pattern                           ║
║    • swarm-refactor.md    - Codebase changes                       ║
║    • file-ops.md          - File operations                        ║
║    • feature-implement.md - Feature workflow                       ║
║    • swarm-debug.md       - Bug investigation                      ║
║    • swarm-review.md      - Code review                            ║
║                                                                    ║
║  Usage: In Claude Code, skills are invoked automatically           ║
║         or via /skill-name                                         ║
╚═══════════════════════════════════════════════════════════════════╝
""")
    return 0


if __name__ == '__main__':
    sys.exit(main())
