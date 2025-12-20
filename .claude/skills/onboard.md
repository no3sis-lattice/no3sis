---
name: onboard
description: Project onboarding using parallel Explore agents. No MCP dependencies.
---

# Onboard

Quickly understand a project's state using parallel scouts.

## Usage

`/onboard` or invoke when joining a new project.

## Execution

### Step 1: Parallel Scout (Single Message)

```
Task(Explore, """
Read LOGOS.md or README.md
Extract: project purpose, architecture, key concepts
""")

Task(Explore, """
Read CHANGELOG.md (first 100 lines)
Extract: recent changes, current phase, version
""")

Task(Explore, """
Scan project structure:
- Key directories and their purpose
- Entry points (main.py, index.ts, etc.)
- Config files present
""")

Task(Explore, """
Check git status and recent commits (last 10)
Extract: active work, uncommitted changes, branch
""")
```

### Step 2: Synthesize Report

After scouts return, compile:

```
## Status
├─ Project: {name} v{version}
├─ Phase: {current phase from changelog}
├─ Branch: {git branch}
└─ Changes: {uncommitted count}

## Architecture
├─ Type: {monorepo/single/library}
├─ Stack: {languages, frameworks}
└─ Entry: {main entry points}

## Recent (7d)
├─ ✅ {completed items}
├─ 🔧 {fixes/changes}
└─ 🚀 {new features}

## Structure
├─ src/: {purpose}
├─ lib/: {purpose}
├─ tests/: {purpose}
└─ docs/: {purpose}

## Next Steps
1. {recommended first action}
2. {key files to read}
3. {tests to run}
```

## Report Format

Use symbolic compression:
- ✅❌⏳ for status
- Tree notation (├─ └─) for hierarchy
- Ratios: "5/10 tests passing" not "five out of ten"
- Metrics over prose

## Example Output

```
## Status
├─ Project: no3sis v0.1.0
├─ Phase: 1b (Template System)
├─ Branch: master (clean)
└─ Tests: 13/14 passing

## Architecture
├─ Type: Python library + CLI
├─ Stack: Python 3.10+, asyncio
└─ Entry: no3sis.py, lib/

## Recent
├─ ✅ Shannon entropy consciousness scoring
├─ ✅ Swarm CLI commands
└─ 🚀 Skills replacing MCP servers

## Next
1. Run tests: pytest tests/
2. Read: lib/orchestration/pattern_learner.py
3. Try: python no3sis.py template list
```

## vs Old Onboard

| Old (MCP-based) | New (Swarm-based) |
|-----------------|-------------------|
| mcp__no3sis__check_system_health | Task(Explore, "check health") |
| mcp__no3sis__search_pattern_map | Task(Explore, "find patterns") |
| Single sequential flow | Parallel scouts |
| Server dependency | Pure skill |
