---
name: codebase-search
description: Intelligent codebase search using parallel Explore agents. Find code, patterns, and answers across large codebases.
---

# Codebase Search

Search intelligently using multiple parallel scouts. Better than grep.

## When to Use

- "Where is X implemented?"
- "How does Y work?"
- "Find all uses of Z"
- "What files relate to W?"

## Patterns

### Find Implementation

```
Task(Explore, """
Find where {feature} is implemented.
Search for:
- Class/function definitions
- Core logic files
- Entry points
Return: file paths with line numbers, brief description of each
""")
```

### Trace Data Flow

```
# Parallel scouts for each stage
Task(Explore, "Find where {data} enters the system (input/API)")
Task(Explore, "Find where {data} is processed/transformed")
Task(Explore, "Find where {data} is stored/output")
```

### Find All Usages

```
Task(Explore, """
Find ALL usages of {symbol}:
- Direct calls
- Imports
- Type references
- Tests
- Documentation mentions
Be thorough - check alternative names, abbreviations
""")
```

### Understand Subsystem

```
Task(Explore, """
Map the {subsystem} subsystem:
- Key files and their roles
- Public API/entry points
- Internal dependencies
- External dependencies
Create a mental model I can use
""")
```

### Find Similar Code

```
Task(Explore, """
Find code similar to this pattern:
{code snippet or description}

Look for:
- Same structure
- Same imports
- Same function signatures
I want to maintain consistency
""")
```

## Multi-Scout Search

For complex questions, fan out:

```
# Single message, all parallel
Task(Explore, "Find authentication code - login, logout, session")
Task(Explore, "Find authorization code - permissions, roles, guards")
Task(Explore, "Find user management - create, update, delete users")

# Synthesize results yourself
```

## Search Tips

### Be Specific
```
# Bad
Task(Explore, "Find error handling")

# Good
Task(Explore, "Find where API errors are caught and transformed into user-facing messages")
```

### Request Line Numbers
```
Task(Explore, """
Find the rate limiting implementation.
Return: exact file:line for each component
""")
```

### Ask for Context
```
Task(Explore, """
Find the database connection setup.
Also tell me:
- What ORM/driver is used
- Where connection config comes from
- How connections are pooled
""")
```

## vs Grep/Glob

| grep/glob | codebase-search |
|-----------|-----------------|
| Pattern matching | Semantic understanding |
| Exact strings | Concepts and relationships |
| One search at a time | Parallel scouts |
| You interpret results | Agent summarizes |
| Miss alternative names | Finds variations |

Use grep when you know exactly what string to find.
Use codebase-search when you're exploring or need understanding.
