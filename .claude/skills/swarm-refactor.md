---
name: swarm-refactor
description: Refactor across multiple files using parallel single-task agents. Use when changes span 3+ files and can be parallelized.
---

# Swarm Refactor

Orchestrate multiple agents to refactor code across many files. Each agent handles ONE file.

## When to Use

- Renaming a function/class across the codebase
- Applying a pattern change to multiple files
- Migrating imports, updating APIs, fixing deprecations
- Any change that touches 3+ files with similar modifications

## The Pattern

```
1. SCOUT   → Explore agent finds all targets
2. PLAN    → You design the atomic change
3. SWARM   → Parallel agents apply to each file
4. VERIFY  → Test runner confirms nothing broke
```

## Execution

### Step 1: Scout (Explore Agent)

Spawn an Explore agent to find all files needing changes:

```
Task(subagent_type="Explore", prompt="""
Find all files that [describe what to find].
Return a simple list of file paths, one per line.
Be thorough - check for variations in naming.
""")
```

### Step 2: Design Atomic Change

Before spawning workers, define the EXACT change as a template:

```markdown
## Change Template
- Find: [exact pattern to match]
- Replace: [exact replacement]
- Context: [any surrounding code to verify]
```

The change must be mechanical - no judgment calls. If agents need to make decisions, the task isn't atomic enough.

### Step 3: Swarm (Parallel Agents)

For each file, spawn a file-creator agent with the atomic task:

```
# Launch ALL agents in a SINGLE message with multiple Task calls
Task(subagent_type="file-creator", prompt="""
File: {file_path}
Task: Apply this exact change:
- Find: {pattern}
- Replace: {replacement}
Only modify this one file. Report what you changed.
""")
```

CRITICAL: Send all Task calls in ONE message to run in parallel.

### Step 4: Verify

After all agents complete:

```
Task(subagent_type="test-runner", prompt="""
Run the test suite. Report any failures.
Focus on tests related to: [the change you made]
""")
```

## Example: Rename Function

User: "Rename getUserData to fetchUserProfile across the codebase"

### Scout
```
Explore: Find all files containing "getUserData" - functions, calls, imports, tests
Result: src/api/user.ts, src/hooks/useUser.ts, tests/user.test.ts (3 files)
```

### Atomic Change
```
Find: getUserData
Replace: fetchUserProfile
Context: function calls, imports, type references
```

### Swarm (single message, 3 parallel agents)
```
file-creator → src/api/user.ts: rename getUserData to fetchUserProfile
file-creator → src/hooks/useUser.ts: rename getUserData to fetchUserProfile
file-creator → tests/user.test.ts: rename getUserData to fetchUserProfile
```

### Verify
```
test-runner → Run tests, check for breakage
```

## Anti-Patterns

- **Don't**: Give one agent all files (defeats parallelism)
- **Don't**: Let agents make design decisions (not atomic)
- **Don't**: Skip the scout phase (you'll miss files)
- **Don't**: Spawn agents sequentially (use single message)

## When NOT to Use

- Changes requiring cross-file coordination
- Refactors needing architectural decisions
- Less than 3 files (just do it directly)
- Changes that depend on each other's results
