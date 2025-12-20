---
name: swarm-dispatch
description: Core pattern for dispatching parallel single-task agents. Use as foundation for any multi-agent workflow.
---

# Swarm Dispatch

The fundamental pattern: break work into atomic tasks, dispatch to specialized agents in parallel.

## Core Principle

**One agent = One task = One outcome**

If an agent needs to make decisions, coordinate with others, or handle multiple concerns, the task isn't atomic enough.

## The Three Laws

1. **Atomic**: Each task has exactly one clear deliverable
2. **Independent**: Tasks don't depend on each other's results
3. **Parallel**: All independent tasks launch in ONE message

## Agent Selection

Match task to specialist:

| Task Type | Agent | Use For |
|-----------|-------|---------|
| Find files/code | `Explore` | Scouting, discovery |
| Create/edit files | `file-creator` | Writing code |
| Review code | `code-hound` | Quality checks |
| Run tests | `test-runner` | Verification |
| Git operations | `git-workflow` | Commits, branches |
| Security check | `security-specialist` | Vuln scanning |
| Write docs | `docs-writer` | Documentation |
| Quick research | `Explore` (quick) | Fast lookups |

## Dispatch Pattern

### Sequential (dependent tasks)
```
Result1 = Task(agent1, task1)
# Wait for result
Result2 = Task(agent2, task2 using Result1)
```

### Parallel (independent tasks)
```
# SINGLE message with multiple Task calls
Task(agent1, task1)
Task(agent2, task2)
Task(agent3, task3)
# All run simultaneously
```

### Fan-out/Fan-in
```
# Scout phase
files = Task(Explore, "find all X")

# Fan-out: parallel workers (SINGLE message)
Task(file-creator, file1)
Task(file-creator, file2)
Task(file-creator, file3)

# Fan-in: verify
Task(test-runner, "verify changes")
```

## Task Prompt Template

Every agent prompt should have:

```markdown
## Context
[What you need to know - 2-3 sentences max]

## Task
[ONE specific action - imperative verb]

## Output
[Exactly what to return - be specific]

## Constraints
[What NOT to do - prevent scope creep]
```

Example:
```markdown
## Context
We're renaming getUserData to fetchUserProfile across the codebase.

## Task
Update src/api/user.ts to use the new function name.

## Output
List the specific lines you changed.

## Constraints
Only modify this file. Don't refactor anything else.
```

## Common Workflows

### Codebase-wide change
```
Explore → find targets
[parallel] file-creator × N → apply changes
test-runner → verify
git-workflow → commit
```

### Feature implementation
```
Plan → design approach
[parallel] file-creator × N → create files
code-hound → review
test-runner → verify
```

### Bug investigation
```
Explore → find relevant code
[parallel] Explore × N → trace through different paths
# Synthesize findings yourself
```

### Documentation update
```
Explore → find code to document
[parallel] docs-writer × N → write docs for each area
```

## Anti-Patterns

| Don't | Do Instead |
|-------|------------|
| One agent, many files | Many agents, one file each |
| Vague prompts | Specific, atomic instructions |
| Sequential when parallel possible | Single message, multiple Tasks |
| Agent makes design choices | You make choices, agent executes |
| Long context in prompts | Minimal context, clear task |

## Measuring Success

Good swarm dispatch:
- Tasks complete without asking questions
- No agent blocks waiting for another
- Results can be combined mechanically
- Failures are isolated to single tasks
