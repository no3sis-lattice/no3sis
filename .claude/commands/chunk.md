---
description: "Process dual-tract chunk (extract → constrain → verify)"
---

Chunk processing pipeline for docs/duality/true-dual-tract/chunks/

**Usage**: `/chunk [chunk-ID]`

**Example**: `/chunk 23` (processes chunk-23-*.md)

## Pipeline

**Sequential execution**:

1. **@boss** → Read chunk metadata
   - Parse YAML front matter
   - Extract category, bott8_class, constraints

2. **@python-specialist** → Run categorization (if needed)
   - scripts/categorize_chunks_71.py
   - Update _category_assignments.json

3. **@minizinc-specialist** → Generate .mzn from constraints
   - Read constraint section from chunk MD
   - Model as MiniZinc decision variables
   - Output: chunk-{ID}.mzn

4. **@minizinc-specialist** → Solve constraint model
   - `minizinc --solver Gecode chunk-{ID}.mzn`
   - Report: SAT/UNSAT/UNKNOWN + solution
   - Generate constraint checksum (SHA256)

5. **@lean-specialist** → Generate/update .lean stub
   - formal/Duality/Chunks/Chunk{ID}.lean
   - Extract axioms from constraints
   - Apply tactics to reduce `sorry` count

6. **@lean-specialist** → Compile Lean proof
   - `cd formal && lake build Duality.Chunks.Chunk{ID}`
   - Report: success/failure + warnings

7. **@pneuma** → Symbolic compression review
   - Analyze constraint notation
   - Compress to maximum Ψ
   - Report context density metric

8. **@docs-writer** → Update chunk outcomes
   - Populate "Outcomes" section in MD
   - Add MiniZinc solution status
   - Add Lean compilation status
   - Add constraint checksum for cross-verification

## Output

**Files Modified**:
- `chunk-{ID}.mzn` (created/updated)
- `Chunk{ID}.lean` (created/updated)
- `chunk-{ID}-*.md` (outcomes section updated)

**Console Report**:
```
🔄 Processing chunk-{ID}

✅ Metadata: category={cat}, bott8_class={N}
✅ MiniZinc: SAT (solution found, 0.023s)
✅ Lean4: Compiled (sorry count: 2/10)
✅ Ψ estimate: 0.78 (context density: high)
📝 Checksum: a3f2c8b9... (for cross-verification)

🎯 Chunk processing complete
```

## Use Cases

- **New chunk**: Full pipeline (generate .mzn + .lean)
- **Update chunk**: Incremental (re-solve + re-compile)
- **Verify chunk**: Check constraint ↔ proof equivalence

## Notes

- Requires docs/duality/ in working directory
- MiniZinc solver: Gecode (default) or Chuffed
- Lean4: lake must be installed (nix develop)
- Cross-verification via `/verify {chunk-ID}`
