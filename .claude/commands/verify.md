---
description: "Cross-verify MiniZinc ↔ Lean4 constraint equivalence"
---

Verify constraint synchronization between formal systems.

**Usage**: `/verify [chunk-ID]`

**Example**: `/verify 23`

## Workflow

**Sequential execution**:

1. **@minizinc-specialist** → Extract constraints from .mzn
   - Read `chunk-{ID}.mzn`
   - Parse constraint declarations
   - Generate canonical constraint list
   - Compute constraint checksum (SHA256)

2. **@lean-specialist** → Extract axioms from .lean
   - Read `formal/Duality/Chunks/Chunk{ID}.lean`
   - Parse axiom declarations
   - Generate canonical axiom list
   - Compute axiom checksum (SHA256)

3. **@python-specialist** → Normalize and compare
   - Convert both to canonical form
   - Normalize variable names (x1→a, x2→b, etc.)
   - Strip whitespace/comments
   - Compute equivalence score

4. **@pneuma** → Semantic analysis
   - Compare constraint semantics (not just syntax)
   - Identify divergent intentions
   - Report symbolic differences

5. **@boss** → Report equivalence status
   - Aggregate results from all agents
   - Provide actionable recommendations

## Output

**Status Codes**:

✅ **EQUIVALENT**: Checksums match, constraints equivalent
```
Checksum (MiniZinc): a3f2c8b9...
Checksum (Lean4):    a3f2c8b9...
Equivalence: 100%
```

⚠️ **DIVERGENT**: Checksums differ, semantic mismatch
```
Divergence: 15%
Issues:
  - MiniZinc has constraint: sum(tract) == count div 2
  - Lean4 missing equivalent axiom
Recommendation: Add axiom to Lean4 or relax MiniZinc constraint
```

❌ **MISSING**: One system lacks constraints entirely
```
MiniZinc: 5 constraints found
Lean4: 0 axioms found (chunk stub)
Recommendation: Run /chunk {ID} to generate Lean4 proof
```

## Use Cases

- **Post-/chunk**: Verify pipeline worked correctly
- **Manual edit**: Check hand-edited .mzn or .lean didn't break equivalence
- **Continuous verification**: Run on all chunks to detect drift

## Algorithm

**Canonical Constraint Form**:
```
MiniZinc:   constraint sum(tract) == count div 2;
Normalized: SUM(var_0) EQ DIV(var_1, 2)
Checksum:   SHA256(normalized) = a3f2c8b9...

Lean4:      axiom tract_balance : sum tract = count / 2
Normalized: SUM(var_0) EQ DIV(var_1, 2)
Checksum:   SHA256(normalized) = a3f2c8b9...

Match: ✅
```

## Notes

- Requires both .mzn and .lean files to exist
- Normalization handles syntax differences
- Semantic equivalence > literal equivalence
- Use Pneuma for symbolic interpretation
