---
name: feature-implement
description: End-to-end feature implementation using swarm agents. Scout → Plan → Implement → Review → Test.
---

# Feature Implementation

Full feature lifecycle using specialized agents.

## Workflow

```
Scout (Explore)     → Understand codebase context
Plan (you)          → Design the implementation
Implement (swarm)   → Parallel file creation
Review (code-hound) → Quality check
Test (test-runner)  → Verify it works
Commit (git-workflow) → Ship it
```

## Execution

### Phase 1: Scout

Understand before building:

```
Task(Explore, """
I'm implementing: {feature description}

Find:
1. Similar existing features (patterns to follow)
2. Files I'll need to modify
3. Files I'll need to create
4. Test patterns used in this codebase
5. Any gotchas or conventions
""")
```

### Phase 2: Plan

Based on scout results, define:

```markdown
## Files to Create
- path/to/new/file.ts - purpose

## Files to Modify
- path/to/existing.ts - what changes

## Dependencies
- What this feature needs
- What needs this feature

## Test Plan
- Unit tests for: X
- Integration tests for: Y
```

### Phase 3: Implement (Parallel)

Single message, multiple agents:

```
# New files (parallel)
Task(file-creator, "Create src/features/auth/login.ts - login logic per plan")
Task(file-creator, "Create src/features/auth/login.test.ts - tests per plan")
Task(file-creator, "Create src/features/auth/types.ts - types per plan")

# Modifications (parallel if independent)
Task(file-creator, "Modify src/routes.ts - add login route per plan")
Task(file-creator, "Modify src/types/index.ts - export auth types")
```

### Phase 4: Review

```
Task(code-hound, """
Review the implementation of {feature}:
- Check for bugs, edge cases
- Verify patterns match codebase conventions
- Check test coverage
- Flag any security concerns
""")
```

### Phase 5: Test

```
Task(test-runner, """
Run tests related to {feature}:
- New tests we added
- Existing tests that might be affected
Report: pass/fail, coverage impact
""")
```

### Phase 6: Commit

```
Task(git-workflow, """
Commit the {feature} implementation:
- Stage relevant files
- Write descriptive commit message
- Don't push yet (let human review)
""")
```

## Example: Add User Settings Page

### Scout
```
Task(Explore, """
I'm adding a user settings page.
Find:
- Existing page components (structure to follow)
- User data access patterns
- Form handling conventions
- How other pages handle save/cancel
""")
```

### Plan
```markdown
## Create
- src/pages/Settings/Settings.tsx
- src/pages/Settings/Settings.test.tsx
- src/pages/Settings/useSettings.ts (hook)

## Modify
- src/routes.tsx (add /settings route)
- src/components/Nav.tsx (add settings link)

## Tests
- Unit: useSettings hook
- Component: Settings renders, form submits
```

### Implement (single message)
```
Task(file-creator, "Create Settings.tsx - form with name, email, password change")
Task(file-creator, "Create Settings.test.tsx - render, submit, validation tests")
Task(file-creator, "Create useSettings.ts - hook for loading/saving settings")
Task(file-creator, "Modify routes.tsx - add /settings pointing to Settings page")
Task(file-creator, "Modify Nav.tsx - add Settings link in user dropdown")
```

### Review
```
Task(code-hound, "Review Settings page implementation")
```

### Test
```
Task(test-runner, "Run: npm test -- --grep Settings")
```

## Anti-Patterns

| Don't | Do |
|-------|-----|
| Implement without scouting | Scout first, understand patterns |
| One agent does everything | Many agents, one task each |
| Skip review | Always run code-hound |
| Skip tests | Always run test-runner |
| Manual git | Use git-workflow agent |

## Scaling Up

For large features, break into sub-features:

```
Feature: User Authentication

Sub-features:
1. Login form → run feature-implement
2. Registration → run feature-implement
3. Password reset → run feature-implement
4. Session management → run feature-implement

Each gets full Scout → Plan → Implement → Review → Test cycle
```
