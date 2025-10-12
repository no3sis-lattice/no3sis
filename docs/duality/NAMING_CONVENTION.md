# Duality Formalization: Naming & Directory Convention

**Last Updated**: 2025-10-12
**Purpose**: Prevent file duplication and location confusion

---

## Directory Structure

```
docs/duality/
├── true-dual-tract/chunks/          # SOURCE & ARTIFACTS
│   ├── chunk-{id}.constraints.json  # Source of truth (canonical)
│   ├── chunk-{id}.mzn               # Generated MiniZinc model
│   ├── chunk-{id}-*.md              # Documentation
│   ├── chunk-{id}.mzn.result.json   # Build artifact (solver results)
│   └── chunk-{id}.lean.proof-status.json  # Build artifact (proof status)
│
└── formal/Duality/Chunks/           # LEAN FORMAL PROJECT
    └── Chunk{id}.lean                # Formal Lean4 module (PascalCase)
```

---

## Naming Rules

### 1. Chunk IDs
- **Format**: Zero-padded 2 digits (01, 06, 19, 62)
- **Range**: 01-99
- **Examples**: `01`, `06`, `19`, `62`

### 2. File Types & Locations

| File Type | Location | Naming | Example |
|-----------|----------|--------|---------|
| **JSON Constraints** | `true-dual-tract/chunks/` | `chunk-{id}.constraints.json` | `chunk-06.constraints.json` |
| **MiniZinc Model** | `true-dual-tract/chunks/` | `chunk-{id}.mzn` | `chunk-06.mzn` |
| **Lean4 Module** | `formal/Duality/Chunks/` | `Chunk{id}.lean` | `Chunk06.lean` |
| **Documentation** | `true-dual-tract/chunks/` | `chunk-{id}-*.md` | `chunk-06-external-operator.md` |
| **Solver Results** | `true-dual-tract/chunks/` | `chunk-{id}.mzn.result.json` | `chunk-06.mzn.result.json` |
| **Proof Status** | `true-dual-tract/chunks/` | `chunk-{id}.lean.proof-status.json` | `chunk-06.lean.proof-status.json` |

### 3. Case Conventions

- **JSON/MZN/Artifacts**: lowercase with dashes (`chunk-06.mzn`)
- **Lean4 Modules**: PascalCase (`Chunk06.lean`)
- **Rationale**: Lean tooling requires PascalCase for module names

---

## ⚠️ IMPORTANT: No Duplication

**DO NOT**:
- ❌ Create `chunk-{id}.lean` in `true-dual-tract/chunks/` (redundant)
- ❌ Create `chunk-{id}.mzn` in `formal/Duality/Chunks/` (wrong location)
- ❌ Use inconsistent capitalization

**Lean files ONLY go in**: `formal/Duality/Chunks/`
**Everything else goes in**: `true-dual-tract/chunks/`

---

## Transpiler Output Paths

### transpile_to_mzn.py
```python
# Output: true-dual-tract/chunks/chunk-{id}.mzn
output_path = base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id}.mzn"
```

### transpile_to_lean.py
```python
# Output: formal/Duality/Chunks/Chunk{id}.lean (PascalCase!)
output_path = base_dir / "formal" / "Duality" / "Chunks" / f"Chunk{chunk_id}.lean"
```

**Verified by**: `shared_utils.py` functions
- `get_chunk_json_path()` → `true-dual-tract/chunks/chunk-{id}.constraints.json`
- `get_chunk_mzn_path()` → `true-dual-tract/chunks/chunk-{id}.mzn`
- `get_chunk_lean_path()` → `formal/Duality/Chunks/Chunk{id}.lean`

---

## CI Validation

The following CI jobs validate naming consistency:

1. **validate-json-schema**: Checks `chunk-*.constraints.json` in `true-dual-tract/chunks/`
2. **validate-minizinc**: Checks `chunk-*.mzn` in `true-dual-tract/chunks/`
3. **validate-lean**: Builds `Chunk*.lean` in `formal/Duality/Chunks/`
4. **cross-check**: Verifies parity across JSON/MZN/Lean

**If you violate naming conventions, CI will fail.**

---

## Rationale

### Why Two Directories?

**`true-dual-tract/chunks/`** - Working directory:
- Contains source + intermediate artifacts
- Used by transpilers, solvers, analysis scripts
- More permissive (allows build artifacts)

**`formal/Duality/Chunks/`** - Formal project:
- Part of Lean4 project structure
- Consumed by `lake build`
- Must follow Lean naming conventions
- Clean (proofs only, no artifacts)

### Why PascalCase for Lean?

Lean4 module system requires:
- File name = Module name
- Modules use PascalCase
- `import Duality.Chunks.Chunk06` expects `Chunk06.lean`

### Why lowercase for everything else?

- Standard Unix convention
- Easier tab-completion
- Consistent with JSON/MZN ecosystems

---

## Migration Guide

If you find files in wrong locations:

```bash
# Remove redundant .lean files from chunks/
cd docs/duality/true-dual-tract/chunks
rm *.lean  # These belong in formal/Duality/Chunks/

# Regenerate if needed
cd ../..
python3 scripts/transpile_to_lean.py --all
```

---

## Quick Reference

**Need to find chunk 06 files?**
```bash
# JSON source
docs/duality/true-dual-tract/chunks/chunk-06.constraints.json

# MiniZinc model
docs/duality/true-dual-tract/chunks/chunk-06.mzn

# Lean4 module
docs/duality/formal/Duality/Chunks/Chunk06.lean

# Documentation
docs/duality/true-dual-tract/chunks/chunk-06-external-operator.md
```

**Need to generate all outputs?**
```bash
cd docs/duality/scripts

# Generate MiniZinc (outputs to true-dual-tract/chunks/)
python3 transpile_to_mzn.py --all

# Generate Lean (outputs to formal/Duality/Chunks/)
python3 transpile_to_lean.py --all
```

---

## Enforcement

- **Scripts**: Use `shared_utils.py` functions (enforces paths)
- **CI**: Validates file locations
- **Code Review**: Check this document before merging

**Last cleanup**: 2025-10-12 - Removed 62 redundant .lean files from `true-dual-tract/chunks/`

---

*Keep this document updated when adding new file types or changing structure.*
