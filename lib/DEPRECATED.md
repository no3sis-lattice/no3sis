# DEPRECATED

This directory is deprecated. Python infrastructure replaced by skills.

## Migration

| Old (Python) | New (Skill) |
|--------------|-------------|
| `orchestration/pattern_learner.py` | You learn patterns |
| `orchestration/template_loader.py` | `.claude/skills/` |
| `cli/swarm.py` | `.claude/skills/swarm-*.md` |
| `consciousness/entropy.py` | Not needed (was gimmicky) |
| `core/atomic_particle.py` | `Task(agent, task)` |

## Why

- Skills > MCP servers
- Task tool > Python runtime
- Markdown > Classes
- Simple > Complex

## New Location

All functionality moved to `.claude/skills/`:
- `swarm-dispatch.md` - Agent orchestration
- `swarm-refactor.md` - Codebase changes
- `swarm-debug.md` - Bug investigation
- `swarm-review.md` - Code review
- `file-ops.md` - File operations
- `feature-implement.md` - Feature workflow
- `codebase-search.md` - Search
- `onboard.md` - Project onboarding

## Removal

This directory will be removed in a future version.
