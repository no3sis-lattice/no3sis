---
description: "Classify chunk by Bott periodicity (0-7, displayed as 1-8)"
---

Assign Bott8 class to chunk based on topological structure.

**Usage**: `/bott8 [chunk-ID]`

**Example**: `/bott8 23`

## Workflow

**Sequential execution**:

1. **@architect** → Analyze chunk topology
   - Read chunk content and metadata
   - Identify operator types (L1-L5 layers)
   - Analyze pipeline structure
   - Detect cyclic patterns

2. **@python-specialist** → Run classification script
   - Execute: `python scripts/assign_bott8_classes.py chunk-{ID}`
   - Load existing: `_bott8_assignments.json`
   - Apply Bott periodicity rules

3. **@lean-specialist** → Verify Bott8 invariants
   - Check if `formal/Duality/Chunks/Chunk{ID}.lean` exists
   - Verify Bott8 axioms in proof (if meta-level chunk)
   - Ensure K-theory periodicity holds

4. **@boss** → Update chunk YAML front matter
   - Modify `chunk-{ID}-*.md` header
   - Set `bott8_class: N` (0-7 internal, 1-8 display)
   - Update `_bott8_assignments.json`
   - Regenerate `_manifest_71.json`

## Bott8 Classes (K-Theory Periodicity)

**0 (display: 1)** - Identity / Trivial bundles
- Return to origin (mod 8 = 0)
- Example: chunk-63 (K-theory foundations)

**1 (display: 2)** - Suspension / Line bundles
- First nontrivial structure
- Example: chunk-64 (vector bundles)

**2 (display: 3)** - Loop space / Quaternionic
- Recursive patterns emerge
- Example: chunk-65 (Clifford algebras)

**3 (display: 4)** - Fiber bundle / Complex structures
- Hierarchical composition
- Example: chunk-66 (stable homotopy)

**4 (display: 5)** - Geometric / Symplectic
- Dimensional reduction
- Example: chunk-67 (8D Riemann manifold)

**5 (display: 6)** - Cohomology / Characteristic classes
- Dual relationships
- Example: chunk-68 (fiber bundles), chunk-69 (characteristic classes)

**6 (display: 7)** - K-theory / Categorical
- Abstract structures
- Example: chunk-70 (index theorem)

**7 (display: 8)** - Spectra / Limit structures
- Periodicity preparation
- Example: chunk-71 (Prime 71 Gandalf - returns to 0)

## Distribution

**Target** (71 chunks, Bott8 balanced):
```
Class 0-6: 9 chunks each (7 × 9 = 63)
Class 7:   8 chunks      (1 × 8 = 8)
Total:     71 chunks
```

**Actual** (from _bott8_assignments.json):
```json
{
  "0": 9,  "1": 9,  "2": 9,  "3": 9,
  "4": 9,  "5": 9,  "6": 9,  "7": 8
}
```

## Output

**Console Report**:
```
🔄 Classifying chunk-23

Topology analysis:
  - Operator type: L3 (internal planning)
  - Pipeline: sequential (3 stages)
  - Cyclic pattern: detected (feedback loop)

Classification:
  - Bott8 class: 2 (Loop space)
  - Justification: Recursive planning with feedback
  - Distribution: Class 2 count = 9 ✅

✅ Updated:
  - chunk-23-*.md (bott8_class: 2)
  - _bott8_assignments.json
  - _manifest_71.json

🎯 Bott8 classification complete
```

## Use Cases

- **New chunk**: Classify during `/chunk` pipeline
- **Reclassify**: Change class based on updated analysis
- **Audit**: Verify all 71 chunks have valid classes
- **Balance**: Ensure distribution matches target [9,9,9,9,9,9,9,8]

## Notes

- Bott8 class is INTERNAL (0-7), DISPLAYED as (1-8)
- Class 7 (display 8) has only 8 chunks (Prime 71: 63 + 8 = 71)
- K-theory periodicity: π_{i+8}(O) ≅ π_i(O)
- Cross-reference: docs/duality/chunk-63-bott8-k-theory.md
