---
description: "Apply Pneuma symbolic compression to code/docs"
---

Compress code/documentation using Axiom I (Context Density).

**Usage**: `/compress [file-path]`

**Examples**:
- `/compress lib/particles/example.py`
- `/compress docs/duality/chunk-23-*.md`
- `/compress .claude/agents/boss.md`

## Workflow

**Sequential execution**:

1. **@pneuma** → Scan for verbosity patterns
   - Identify redundancy (repeated phrases)
   - Find low-density sections (prose > pattern)
   - Detect compression opportunities

2. **@pneuma** → Apply CIG³ compression
   - **Φ (Local)**: Extract semantic features
   - **Σ (Spectral)**: Find low-rank structure
   - **Π (Topology)**: Preserve persistent invariants
   - **Ψ (Invariant)**: Compress to max context density

3. **@pneuma** → Generate compressed version
   - Symbolic notation where applicable
   - Pattern-based restructuring
   - Tree notation (├─ └─) for hierarchies
   - Preserve semantic meaning

4. **@code-hound** → Verify no semantic loss
   - For code: Run tests before/after
   - For docs: Check all references intact
   - For proofs: Verify tactics still valid

5. **@boss** → Show entropy reduction metric
   - Calculate compression ratio
   - Report Ψ estimate
   - Provide diff summary

## Compression Targets

**Python Code**:
```python
# Before (verbose comments)
# This function processes the user input by first validating it,
# then transforming it into the correct format, and finally
# returning the processed result to the caller.

# After (symbolic annotation)
# @P.validate → @P.transform → @P.return
```

**Markdown Documentation**:
```markdown
# Before
- First item explanation with details
- Second item explanation with details
- Third item explanation with details

# After (symbolic)
├─ Item 1: detail
├─ Item 2: detail
└─ Item 3: detail
```

**Lean4 Proofs**:
```lean
-- Before
theorem example : P := by
  sorry
  sorry
  sorry

-- After (compressed tactics)
theorem example : P := by simp [lemma1, lemma2]; exact proof
```

## Output

**Console Report**:
```
🔄 Compressing: lib/particles/example.py

Original:   1,247 chars (42 lines)
Compressed:   623 chars (28 lines)

Entropy reduction: 0.50 (50% compression)
Ψ estimate: 0.82 (very high context density)

Changes:
  - Removed 5 verbose comments
  - Converted 3 docstrings to symbolic form
  - Compressed 2 function chains to composition

✅ Semantic equivalence verified (tests pass)

📝 Compressed version written to: example.compressed.py
   Review and replace if satisfied.
```

## Options

**--in-place**: Overwrite original file (dangerous!)
```
/compress lib/example.py --in-place
```

**--preview**: Show diff without writing
```
/compress lib/example.py --preview
```

**--metric**: Calculate Ψ only, no compression
```
/compress lib/example.py --metric
```

## Use Cases

- **Agent prompts**: Compress .claude/agents/*.md (like boss.md 586→173 lines)
- **Documentation**: Apply to verbose docs
- **Code review**: Identify low-density code sections
- **Proof optimization**: Reduce sorry count in Lean4

## Notes

- Always creates `.compressed` version first (safety)
- Run tests before accepting compression
- Pneuma applies Three Axioms (Bifurcation, Map, Emergence)
- Target Ψ ≥ 0.7 for "acceptable" compression
