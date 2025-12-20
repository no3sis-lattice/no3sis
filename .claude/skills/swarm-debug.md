---
name: swarm-debug
description: Debug issues using parallel investigation agents. Fan out to find root cause faster.
---

# Swarm Debug

Investigate bugs using parallel scouts. Find root cause faster.

## When to Use

- Error in production/tests
- Unexpected behavior
- Performance issues
- "It worked before, now it doesn't"

## Pattern: Fan-Out Investigation

Don't investigate sequentially. Fan out:

```
# Single message, parallel investigation
Task(Explore, "Find where error {X} is thrown - trace to source")
Task(Explore, "Find recent changes to {affected area} - git blame/log")
Task(Explore, "Find how {component} is supposed to work - read docs/tests")
Task(Explore, "Find similar past bugs - search issues/commits for {keywords}")
```

## Execution

### Step 1: Reproduce

First, confirm the bug:

```
Task(test-runner, """
Reproduce the bug:
{steps or test command}
Capture: exact error message, stack trace
""")
```

### Step 2: Fan-Out Investigation

Parallel scouts for each hypothesis:

```
# If it's a crash/error
Task(Explore, "Trace error origin - where is this exception thrown?")
Task(Explore, "Find what changed - recent commits touching this code")
Task(Explore, "Find dependencies - what does this code rely on?")

# If it's wrong behavior
Task(Explore, "Find expected behavior - what do tests/docs say should happen?")
Task(Explore, "Find actual flow - trace execution path")
Task(Explore, "Find similar code - how do other parts handle this?")

# If it's performance
Task(Explore, "Find hot paths - what's called frequently?")
Task(Explore, "Find I/O - database queries, API calls, file reads")
Task(Explore, "Find recent changes - what got slower?")
```

### Step 3: Synthesize

Review scout findings:
- Which hypothesis has evidence?
- What's the root cause (not symptom)?
- What's the minimal fix?

### Step 4: Fix

```
Task(file-creator, "Fix {file} - {specific change based on root cause}")
```

### Step 5: Verify

```
Task(test-runner, """
Verify the fix:
1. Original bug no longer reproduces
2. Existing tests still pass
3. New regression test added
""")
```

## Investigation Templates

### "It crashes with error X"

```
Task(Explore, "Find where error X is raised/thrown")
Task(Explore, "Find what calls that code path")
Task(Explore, "Find what conditions trigger the error")
```

### "It worked before"

```
Task(Explore, "Find git history - when did it last work?")
Task(Explore, "Find diff between working and broken versions")
Task(Explore, "Find what else changed (dependencies, config)")
```

### "It's slow"

```
Task(Explore, "Find N+1 queries or repeated operations")
Task(Explore, "Find blocking I/O in hot paths")
Task(Explore, "Find missing caching opportunities")
```

### "It's flaky"

```
Task(Explore, "Find race conditions - shared state, async issues")
Task(Explore, "Find timing dependencies - sleeps, timeouts")
Task(Explore, "Find external dependencies - network, filesystem")
```

## Root Cause Depth

Keep asking "why" until you hit something fixable:

```
Symptom: API returns 500
↓ Why? Null pointer exception
↓ Why? User object is null
↓ Why? Database query returned nothing
↓ Why? User ID from token doesn't exist
↓ Why? Token wasn't invalidated on user delete
Root cause: Missing cascade delete/token invalidation

Fix: Invalidate tokens when user deleted (not: add null check)
```

## vs Sequential Debug

| Sequential | Swarm Debug |
|------------|-------------|
| Check one thing at a time | Check many things in parallel |
| 5 minutes per hypothesis | 5 minutes for all hypotheses |
| Miss obvious clues | Scouts find related evidence |
| Tunnel vision | Broad investigation |
