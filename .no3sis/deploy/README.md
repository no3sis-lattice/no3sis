# Synapse Deploy Scripts

## Current System (Simplified)

The new simplified setup uses a single CLI script:

```bash
# Main synapse CLI
~/.synapse-system/synapse

# Commands:
synapse start    # Start Neo4j + Redis services
synapse stop     # Stop services
synapse status   # Check health
synapse init     # Setup project with agents
synapse search   # Search global knowledge
```

### Project Setup
```bash
# Initialize any project with language-specific agents
cd your-project/
~/.synapse-system/synapse init .

# Creates:
# - .claude/agents/language-specialist.md
# - .claude/agents/synapse-project-manager.md
# - .synapse.yml (project config)
```

## Legacy Scripts (Deprecated)

The `legacy/` directory contains the old complex setup system:

- `init-project.sh` - 545 lines of complex project initialization
- `setup-claude-code.sh` - 400+ lines with bash heredoc issues
- `simple-setup.sh` - Wrapper that was not actually simple

**These are preserved for reference but should not be used.**

## Active Scripts

- `sync-global.sh` - Still used for syncing global knowledge base updates

## Architecture

**New (Global-First):**
- Global synapse services (Neo4j, Redis)
- Projects get agents + config only
- All search uses global knowledge base
- Simple, predictable, works

**Old (Broken):**
- Tried to create local synapse per project
- Complex dependency management
- Broken Python environments
- Multiple nested scripts calling each other

## Migration

Projects using old setup should be re-initialized:

```bash
# Remove old .synapse directory if it exists
rm -rf .synapse

# Use new simple setup
~/.synapse-system/synapse init .
```