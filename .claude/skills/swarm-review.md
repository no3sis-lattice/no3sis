---
name: swarm-review
description: Code review using parallel specialist agents. Thorough review in less time.
---

# Swarm Review

Review code changes using specialized parallel agents.

## When to Use

- Before merging PR
- After implementing feature
- Reviewing someone else's code
- Pre-commit quality check

## Parallel Review Agents

Different agents check different aspects:

```
# Single message, all parallel
Task(code-hound, """
Review for correctness and design:
- Logic bugs
- Edge cases missed
- SOLID violations
- DRY violations
""")

Task(security-specialist, """
Review for security:
- Input validation
- Auth/authz issues
- Injection vulnerabilities
- Secrets exposure
""")

Task(test-runner, """
Check test coverage:
- Run existing tests
- Identify untested paths
- Suggest missing tests
""")

Task(Explore, """
Check consistency:
- Does this match existing patterns?
- Are naming conventions followed?
- Is documentation updated?
""")
```

## Review Checklists

### Correctness (code-hound)
- [ ] Logic handles all cases
- [ ] Error handling present
- [ ] Edge cases covered
- [ ] No obvious bugs

### Security (security-specialist)
- [ ] Input validated
- [ ] No hardcoded secrets
- [ ] Auth checks present
- [ ] No injection risks

### Quality (code-hound)
- [ ] Single responsibility
- [ ] No code duplication
- [ ] Clear naming
- [ ] Appropriate abstraction level

### Tests (test-runner)
- [ ] Tests pass
- [ ] New code has tests
- [ ] Edge cases tested
- [ ] No flaky tests added

### Consistency (Explore)
- [ ] Matches existing patterns
- [ ] Follows conventions
- [ ] Documentation updated
- [ ] No unnecessary changes

## Execution

### Step 1: Understand Scope

```
Task(Explore, """
What does this change do?
- Files modified
- Features added/changed
- Dependencies added
""")
```

### Step 2: Parallel Review

```
Task(code-hound, "Review {files} for correctness, design, quality")
Task(security-specialist, "Review {files} for security issues")
Task(test-runner, "Run tests, check coverage for {files}")
```

### Step 3: Synthesize Findings

Combine agent findings into:

```markdown
## Review Summary

### ✅ Approved
- {things that look good}

### ⚠️ Suggestions
- {non-blocking improvements}

### ❌ Blockers
- {must fix before merge}

### 📝 Nits
- {minor style/formatting}
```

## Review Depth Levels

### Quick (pre-commit)
```
Task(test-runner, "Run tests")
Task(code-hound, "Quick scan for obvious issues")
```

### Standard (PR review)
```
Task(code-hound, "Full review for correctness and design")
Task(test-runner, "Run tests, check coverage")
Task(Explore, "Check consistency with codebase")
```

### Deep (critical code)
```
Task(code-hound, "Deep review - correctness, design, edge cases")
Task(security-specialist, "Security audit")
Task(test-runner, "Full test suite, mutation testing if available")
Task(Explore, "Check against architecture docs")
Task(Explore, "Find similar code - ensure consistency")
```

## Responding to Review

When you receive review feedback:

```
# For each finding
Task(file-creator, "Fix: {issue} in {file}")

# After fixes
Task(test-runner, "Verify fixes don't break anything")
Task(code-hound, "Re-review fixed areas")
```

## vs Single Reviewer

| Single Reviewer | Swarm Review |
|-----------------|--------------|
| One perspective | Multiple specialties |
| Sequential checking | Parallel checking |
| Fatigue after 200 lines | Each agent focused |
| Miss security/test gaps | Dedicated specialists |
