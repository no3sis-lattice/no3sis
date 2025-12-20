# DEPRECATED

This directory is deprecated. Templates have been replaced by skills.

## Migration

| Old (Template) | New (Skill) |
|----------------|-------------|
| `file_creator/` | `.claude/skills/file-ops.md` |
| `metadata.json` | Inline in skill |
| Python particles | `Task(file-creator, ...)` |

## Why

- Skills are simpler (markdown vs Python classes)
- No runtime/server needed
- Parallel agents via Task tool
- Easier to maintain and share

## New Location

See `.claude/skills/` for all skills:
- `file-ops.md` - File operations
- `batch-file-create.md` - Scaffolding
- `swarm-dispatch.md` - Core pattern

## Removal

This directory will be removed in a future version.
