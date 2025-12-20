---
name: file-ops
description: File system operations using parallel agents. Replaces file_creator template with swarm pattern.
---

# File Operations (Swarm)

Orchestrate file operations using single-task agents. No Python runtime needed.

## Operations

### Create Files (Parallel)

```
# Single message, all parallel
Task(file-creator, "Create src/utils/helpers.ts with: [content]")
Task(file-creator, "Create src/utils/helpers.test.ts with: [content]")
Task(file-creator, "Create src/utils/index.ts exporting helpers")
```

### Read Files (Parallel Scout)

```
Task(Explore, """
Read and summarize these files:
- src/config.ts
- src/types.ts
Return: key exports, patterns used, dependencies
""")
```

### Move/Rename (Sequential)

Moving requires knowing source exists:
```
# Scout first
files = Task(Explore, "Find all files matching **/old-name.*")

# Then move each (parallel)
Task(file-creator, "Move src/old-name.ts to src/new-name.ts")
Task(file-creator, "Move src/old-name.test.ts to src/new-name.test.ts")

# Update imports (parallel)
Task(file-creator, "Update imports in src/index.ts: old-name → new-name")
```

### Delete (With Safety)

```
# Scout to confirm targets
Task(Explore, "List all files in src/deprecated/ - confirm deletion targets")

# Delete after confirmation (you decide, not agent)
Task(file-creator, "Delete src/deprecated/old-module.ts")
```

### Batch Create (Template-Based)

For scaffolding with patterns:

```
# Define template inline
template = """
// {component}.tsx
export function {component}() { return <div>{component}</div> }
"""

# Fan out
Task(file-creator, "Create Button.tsx using template: {template}")
Task(file-creator, "Create Card.tsx using template: {template}")
Task(file-creator, "Create Modal.tsx using template: {template}")
```

## Patterns

### Component Scaffold
```
manifest:
  - {Name}/{Name}.tsx        # Component
  - {Name}/{Name}.test.tsx   # Tests
  - {Name}/{Name}.styles.ts  # Styles
  - {Name}/index.ts          # Export

dispatch:
  Task(file-creator, "{Name}.tsx - React FC with props")
  Task(file-creator, "{Name}.test.tsx - RTL tests")
  Task(file-creator, "{Name}.styles.ts - styled-components")
  Task(file-creator, "index.ts - re-export")
```

### API Module Scaffold
```
manifest:
  - api/{resource}/types.ts
  - api/{resource}/queries.ts
  - api/{resource}/mutations.ts
  - api/{resource}/index.ts

dispatch:
  Task(file-creator, "types.ts - TS interfaces")
  Task(file-creator, "queries.ts - GET functions")
  Task(file-creator, "mutations.ts - POST/PUT/DELETE")
  Task(file-creator, "index.ts - exports")
```

### Config Generation
```
# Read existing patterns first
Task(Explore, "Read tsconfig.json, package.json - extract project conventions")

# Generate matching new config
Task(file-creator, "Create .eslintrc following project conventions")
```

## vs Old Template System

| file_creator Template | file-ops Skill |
|----------------------|----------------|
| Python classes (FileWriter, FileReader...) | Agent prompts |
| metadata.json schema | Inline patterns |
| Particle runtime | Task tool |
| Corpus callosum routing | Direct dispatch |
| Pattern learning (magic) | You learn patterns |

The skill is simpler: describe what you want, agents do it.
