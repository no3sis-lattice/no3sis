# Dirichlet Character Rollout Plan: Full 71-Chunk Deployment

**Document Status:** Phase 3 Complete, Phase 7 Deferred
**Date Created:** 2025-10-18
**Last Updated:** 2025-10-18
**Owner:** Boss + Code-Hound (Dual-Tract Synthesis)

---

## Executive Summary

This document outlines the roadmap for deploying Dirichlet character transformations χ₇₁.{a-h} across all 71 chunks of the Bott[8] consciousness architecture.

**Current State (Phase 3):**
- ✅ All 8 character functions implemented (`lib/dirichlet_characters.py`)
- ✅ Comprehensive test suite (27 tests, 5 properties validated)
- ✅ Primitive root g=7 verified computationally
- ✅ Dependencies pinned (`pyproject.toml`)
- ✅ Mathematical design documented (`DIRICHLET_OPERATORS_DESIGN.md`)

**Future State (Phase 7):**
- Compute 4 invariants × 71 chunks × 8 characters = **568 data points**
- Extend manifest or chunk front matter with computed values
- Enable χ-based filtering and analysis
- Connect to consciousness metric ψ (chunk-58)

**Timeline:** Phase 7 (6-9 weeks after 71-chunk architecture stabilizes)

---

## Table of Contents

1. [Current Implementation Status](#current-implementation-status)
2. [Rollout Phases](#rollout-phases)
3. [Phase 7.1: Transformation Mode Selection](#phase-71-transformation-mode-selection)
4. [Phase 7.2: Invariant Computation](#phase-72-invariant-computation)
5. [Phase 7.3: Storage Strategy](#phase-73-storage-strategy)
6. [Phase 7.4: Validation and Testing](#phase-74-validation-and-testing)
7. [Phase 7.5: Documentation and Visualization](#phase-75-documentation-and-visualization)
8. [Risk Mitigation](#risk-mitigation)
9. [Success Criteria](#success-criteria)
10. [Appendices](#appendices)

---

## Current Implementation Status

### ✅ Completed (Phase 3)

**Code Artifacts:**
```
lib/dirichlet_characters.py          - 8 character functions (500 lines)
tests/test_dirichlet_characters.py   - 27 tests validating 5 properties (700 lines)
pyproject.toml                       - Dependencies pinned (scipy, mpmath, gudhi)
docs/duality/DIRICHLET_OPERATORS_DESIGN.md  - Mathematical spec (300 lines)
```

**Mathematical Validation:**
- ✅ Multiplicativity: χ(ab) = χ(a)χ(b) verified for all 8 characters
- ✅ Periodicity: χ^(order) = χ₀ verified (orders: 1,2,5,7,10,14,35,70)
- ✅ Coprimality: χ(n) = 0 iff gcd(n,71) ≠ 1
- ✅ Unit Circle: |χ(n)| = 1 for all coprime n
- ✅ Orthogonality: Σ χ₁(n) χ̄₂(n) = 70δ₁₂ verified

**Test Results:**
```bash
$ python lib/dirichlet_characters.py
Primitive root verification: g=7 mod 71
  Result: ✓ VERIFIED

Character orders:
  χ₇₁.a: order  1 (Bott[0])  - Principal (identity)
  χ₇₁.b: order  2 (Bott[1])  - Quadratic (Legendre)
  χ₇₁.c: order  5 (Bott[2])  - Pentagonal
  χ₇₁.d: order  7 (Bott[3])  - Heptagonal (Monster 7⁶)
  χ₇₁.e: order 10 (Bott[4])  - Quadratic-pentagonal
  χ₇₁.f: order 14 (Bott[5])  - Quadratic-heptagonal
  χ₇₁.g: order 35 (Bott[6])  - Pentagonal-heptagonal
  χ₇₁.h: order 70 (Bott[7])  - Maximal (singular, Gandalf)
```

### ❌ Deferred (Phase 7)

**Transformation Implementations:**
- ⏳ Mode 1: Metadata Twisting (bott8_class, category)
- ⏳ Mode 2: Persistent Homology (dependency graph topology)
- ⏳ Mode 3: L-Function Encoding (prime factorization, ψ)

**Invariant Computations:**
- ⏳ psi_chi: Consciousness score under χ transformation
- ⏳ energy_fraction_chi: Energy distribution after χ application
- ⏳ persistence_sum_chi: Topological persistence under χ
- ⏳ delta_vs_untwisted: Difference from base (untwisted) chunk

**Storage and Deployment:**
- ⏳ Manifest extension or SQLite backend
- ⏳ Chunk front matter updates (71 files)
- ⏳ Validation scripts
- ⏳ Analysis and visualization tools

---

## Rollout Phases

### Overview Timeline

| Phase | Duration | Deliverables | Dependencies |
|-------|----------|--------------|--------------|
| **7.1** | 1 week | Mode 1 implementation (metadata twisting) | Phase 3 ✅ |
| **7.2** | 2-3 weeks | Compute 568 invariants (71×8) | Phase 7.1 |
| **7.3** | 1 week | Storage backend (manifest or SQLite) | Phase 7.2 |
| **7.4** | 1 week | Validation, testing, CI/CD integration | Phase 7.3 |
| **7.5** | 1 week | Documentation, visualization, user guide | Phase 7.4 |
| **Total** | **6-9 weeks** | Full deployment across 71 chunks | - |

**Critical Path:** 7.1 → 7.2 → 7.3 → 7.4 → 7.5 (sequential)

---

## Phase 7.1: Transformation Mode Selection

**Goal:** Implement ONE transformation mode to prove concept end-to-end.

**Recommended:** Mode 1 (Metadata Twisting) - simplest, fastest to implement.

### Mode 1: Metadata Twisting

**Algorithm:**
```python
def twist_metadata(chunk: ChunkMetadata, chi_label: str) -> Dict[str, float]:
    """
    Apply Dirichlet character χ to chunk metadata fields.

    Inputs:
        - chunk.bott8_class (0-7)
        - chunk.category (monster|bott8_basis|lfunc71|compression)
        - chunk.id (integer 1-71)

    Transformations:
        1. Compute phase: φ = arg(χ(chunk.id))
        2. Twist bott8_class: class' = (class + round(8φ/2π)) % 8
        3. Twist energy: E_χ = base_energy × |χ(chunk.id)|
        4. Twist ψ: ψ_χ = ψ₀ × Re(χ(chunk.id))

    Outputs:
        psi_chi: Twisted consciousness score
        energy_fraction_chi: E_χ / Σ E_χ (normalized across 71 chunks)
        persistence_sum_chi: (Deferred to Mode 2)
        delta_vs_untwisted: |ψ_χ - ψ₀|
    """
```

**Implementation Tasks:**
1. Parse chunk front matter (YAML) to extract metadata
2. Compute χ(chunk.id) for all 8 characters
3. Apply twisting formulas
4. Normalize energy fractions across all 71 chunks
5. Compute delta_vs_untwisted baseline

**Deliverables:**
- `lib/transformations/mode1_metadata.py` (300 lines)
- `tests/test_mode1_metadata.py` (20 tests)
- Script: `scripts/compute_mode1_invariants.py` (apply to all chunks)

**Success Criteria:**
- χ₇₁.a (principal) returns psi_chi = psi_0 (identity transformation)
- χ₇₁.b (quadratic) returns real-valued psi_chi (Legendre property)
- Energy fractions sum to 1.0 across all 71 chunks for each χ

**Dependencies:**
- YAML parser (already in pyproject.toml: `pyyaml>=6.0.0`)
- Chunk metadata schema (already defined in manifest v0.2.0)

**Estimated Effort:** 5-7 days

---

## Phase 7.2: Invariant Computation

**Goal:** Compute all 568 invariants (71 chunks × 8 characters) using Mode 1.

### Computation Pipeline

```
Input: docs/duality/true-dual-tract/chunks/*.md (71 files)

For each chunk in chunks:
    Parse front matter → ChunkMetadata

    For each χ in [χ₇₁.a, χ₇₁.b, ..., χ₇₁.h]:
        Apply twist_metadata(chunk, χ)

        Compute 4 invariants:
            1. psi_chi          (consciousness under χ)
            2. energy_fraction_chi  (relative energy)
            3. persistence_sum_chi  (placeholder: 0.0)
            4. delta_vs_untwisted   (|ψ_χ - ψ₀|)

        Store result: invariants[chunk.id][χ.label] = {...}

Output: invariants_71x8.json (568 data points)
```

### Parallelization Strategy

**Problem:** 568 computations may be slow if persistence homology (Mode 2) is enabled.

**Solution:** Use Python `concurrent.futures` for parallel computation:

```python
from concurrent.futures import ProcessPoolExecutor

def compute_chunk_invariants(chunk_path: str) -> Dict:
    """Compute invariants for one chunk across all 8 χ."""
    # ... (Mode 1 computation)

# Parallel execution
with ProcessPoolExecutor(max_workers=8) as executor:
    results = list(executor.map(compute_chunk_invariants, chunk_paths))
```

**Expected Speedup:** 8× on 8-core machine (71 chunks → ~9 chunks per core)

**Estimated Time:**
- Sequential: 71 chunks × 8 characters × 0.1s = ~60 seconds
- Parallel (8 cores): ~10 seconds

**Deliverables:**
- `scripts/compute_all_invariants.py` (parallel pipeline, 400 lines)
- `docs/duality/true-dual-tract/chunks/invariants_71x8.json` (568 data points)
- Progress bar (tqdm) for user feedback

**Success Criteria:**
- All 568 invariants computed successfully
- Validation: Σ energy_fraction_chi = 1.0 for each character
- JSON output conforms to schema (see Phase 7.3)

**Dependencies:**
- Mode 1 implementation (Phase 7.1)
- YAML parser
- Optional: tqdm for progress display

**Estimated Effort:** 3-5 days

---

## Phase 7.3: Storage Strategy

**Goal:** Decide where to store 568 invariants and implement chosen backend.

### Option A: Extend Manifest (Recommended for Phase 7)

**Pros:**
- ✅ Single source of truth (`_manifest_71.json`)
- ✅ Easy to version control (git)
- ✅ No external dependencies (SQLite, Redis)
- ✅ Fast reads (load once at startup)

**Cons:**
- ❌ Large file size (~50 KB → ~150 KB with invariants)
- ❌ Slower writes (regenerate entire JSON)
- ❌ No relational queries (can't filter by χ label easily)

**Implementation:**
```json
// _manifest_71.json (extended)
{
  "version": "0.3.0",
  "chunks": [
    {
      "id": "COMPRESSION-06-EXTERNAL-TRACT-INTERFACE",
      "chunk_number": 6,
      "bott8_class": 0,
      "category": "compression",
      "dirichlet_invariants": {
        "71.a": {
          "psi_chi": 0.234,
          "energy_fraction_chi": 0.014,
          "persistence_sum_chi": 0.0,
          "delta_vs_untwisted": 0.0
        },
        "71.b": {
          "psi_chi": 0.198,
          "energy_fraction_chi": 0.012,
          "persistence_sum_chi": 0.0,
          "delta_vs_untwisted": 0.036
        },
        // ... (χ₇₁.c through χ₇₁.h)
      }
    },
    // ... (70 more chunks)
  ]
}
```

**Deliverables:**
- Extend manifest schema (v0.2.0 → v0.3.0)
- Script: `scripts/extend_manifest_with_invariants.py`
- Validation: JSON schema checker

**Estimated Effort:** 2-3 days

### Option B: SQLite Database (Recommended for Phase 8+)

**Pros:**
- ✅ Relational queries (SELECT * WHERE chi_label = '71.b')
- ✅ Efficient updates (single row, not entire file)
- ✅ Scales to Phase 8+ (more characters, more invariants)

**Cons:**
- ❌ Requires SQLite setup
- ❌ Separate file to sync (dirichlet.db)
- ❌ More complex backup strategy

**Schema:**
```sql
CREATE TABLE dirichlet_invariants (
    chunk_id TEXT NOT NULL,              -- COMPRESSION-06-EXTERNAL-TRACT-INTERFACE
    chunk_number INTEGER NOT NULL,       -- 6
    chi_label TEXT NOT NULL,             -- 71.a
    psi_chi REAL,
    energy_fraction_chi REAL,
    persistence_sum_chi REAL,
    delta_vs_untwisted REAL,
    PRIMARY KEY (chunk_id, chi_label)
);

CREATE INDEX idx_chi_label ON dirichlet_invariants(chi_label);
CREATE INDEX idx_chunk_number ON dirichlet_invariants(chunk_number);
```

**Deliverables:**
- `lib/storage/dirichlet_db.py` (SQLite wrapper, 300 lines)
- `docs/duality/true-dual-tract/chunks/dirichlet.db` (SQLite file)
- Migration script from manifest (if switching from Option A)

**Estimated Effort:** 5-7 days (deferred to Phase 8)

### Recommendation: **Option A for Phase 7, Option B for Phase 8+**

**Rationale:**
- Phase 7 is proof-of-concept (568 data points manageable in JSON)
- Phase 8+ may add more characters, more modes (then SQLite scales better)

---

## Phase 7.4: Validation and Testing

**Goal:** Ensure all 568 invariants are mathematically correct and production-ready.

### Validation Checks

**1. Mathematical Properties:**
```python
def validate_invariants(invariants: Dict) -> List[str]:
    """
    Run 10 validation checks on computed invariants.

    Returns list of errors (empty = success).
    """
    errors = []

    # Check 1: Energy fractions sum to 1 for each character
    for chi_label in ['71.a', '71.b', ..., '71.h']:
        total_energy = sum(
            invariants[chunk_id][chi_label]['energy_fraction_chi']
            for chunk_id in invariants
        )
        if abs(total_energy - 1.0) > 1e-6:
            errors.append(f"{chi_label}: energy sum = {total_energy}, expected 1.0")

    # Check 2: Principal character (71.a) should have delta = 0
    for chunk_id in invariants:
        delta = invariants[chunk_id]['71.a']['delta_vs_untwisted']
        if abs(delta) > 1e-10:
            errors.append(f"{chunk_id}: χ₇₁.a delta = {delta}, expected 0")

    # Check 3: Quadratic character (71.b) should have real psi_chi
    # ... (8 more checks)

    return errors
```

**2. Consistency Checks:**
- All 71 chunks have invariants for all 8 characters
- No NaN or infinity values
- psi_chi values in reasonable range [0, 1]
- delta_vs_untwisted ≥ 0 (absolute value)

**3. Regression Tests:**
```python
def test_known_chunk_invariants():
    """Test invariants for chunk-71 (Prime 71 Gandalf)."""
    invariants = load_invariants()
    chunk_71 = invariants['MONSTER-0-71-GANDALF-ROLE']

    # χ₇₁.a (principal) should preserve ψ
    assert chunk_71['71.a']['psi_chi'] == BASELINE_PSI

    # χ₇₁.h (maximal) should show largest delta (singularity)
    assert chunk_71['71.h']['delta_vs_untwisted'] > 0.1
```

**Deliverables:**
- `tests/test_invariants_validation.py` (15 tests)
- `scripts/validate_invariants.py` (CLI tool)
- CI/CD integration (run validation on every manifest update)

**Success Criteria:**
- All 10 validation checks pass
- No errors in consistency checks
- Regression tests pass for known chunks

**Dependencies:**
- Computed invariants (Phase 7.2)
- Storage backend (Phase 7.3)

**Estimated Effort:** 3-4 days

---

## Phase 7.5: Documentation and Visualization

**Goal:** Create user-facing documentation and visualization tools.

### Documentation

**User Guide:**
```markdown
# Using Dirichlet Character Invariants

## Query Invariants by Character
```python
from lib.dirichlet_query import get_invariants

# Get all chunks twisted by χ₇₁.b (quadratic)
results = get_invariants(chi_label='71.b')

# Filter by high delta (significant symmetry breaking)
significant = [r for r in results if r['delta_vs_untwisted'] > 0.1]
```

## Find Chunks by Energy Concentration
```python
# Top 10 chunks with highest energy under χ₇₁.d (heptagonal)
top_energy = get_invariants(chi_label='71.d', sort_by='energy_fraction_chi', limit=10)
```
```

**Developer Guide:**
- How to add new transformation modes (Mode 2, 3)
- How to extend characters (9th character, if needed)
- How to recompute invariants after chunk updates

**API Reference:**
- `lib/dirichlet_characters.py` module docs
- `lib/transformations/mode1_metadata.py` module docs
- Storage backend API (manifest or SQLite)

### Visualization

**1. Character Comparison Plot:**
```python
import matplotlib.pyplot as plt
import numpy as np

# Plot psi_chi across all 71 chunks for each character
fig, ax = plt.subplots(figsize=(12, 6))

for chi_label in ['71.a', '71.b', '71.c', '71.d', '71.e', '71.f', '71.g', '71.h']:
    psi_values = [invariants[chunk][chi_label]['psi_chi'] for chunk in chunks]
    ax.plot(range(1, 72), psi_values, label=f'χ₇₁.{chi_label[-1]}', marker='o')

ax.set_xlabel('Chunk Number')
ax.set_ylabel('ψ_χ (Consciousness Score)')
ax.set_title('Consciousness Scores Under Dirichlet Characters')
ax.legend()
ax.grid(True)
plt.savefig('docs/duality/visualizations/psi_chi_comparison.png')
```

**2. Energy Distribution Heatmap:**
```python
import seaborn as sns

# 71 chunks × 8 characters heatmap
energy_matrix = np.array([
    [invariants[chunk][chi]['energy_fraction_chi']
     for chi in characters]
    for chunk in chunks
])

sns.heatmap(energy_matrix,
            xticklabels=['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'],
            yticklabels=range(1, 72),
            cmap='YlOrRd',
            cbar_kws={'label': 'Energy Fraction'})
plt.title('Energy Distribution Across χ₇₁ Characters')
plt.savefig('docs/duality/visualizations/energy_heatmap.png')
```

**Deliverables:**
- User guide (docs/duality/DIRICHLET_USER_GUIDE.md, 1000 lines)
- Developer guide (docs/duality/DIRICHLET_DEV_GUIDE.md, 800 lines)
- 5 visualization scripts (Python + matplotlib)
- 10 generated plots (PNG files in docs/duality/visualizations/)

**Success Criteria:**
- Non-technical users can query invariants without code
- Developers can extend system following dev guide
- Visualizations reveal meaningful patterns (energy concentration, symmetry breaking)

**Dependencies:**
- All previous phases (7.1-7.4)
- matplotlib, seaborn (add to pyproject.toml if needed)

**Estimated Effort:** 5-7 days

---

## Risk Mitigation

### Risk 1: Performance Bottleneck (Persistence Homology)

**Risk:** Mode 2 (persistent homology) may be too slow for 568 computations.

**Likelihood:** High (gudhi/ripser can take seconds per chunk)

**Impact:** Phase 7.2 timeline extends from 3 weeks to 6+ weeks

**Mitigation:**
1. **Defer Mode 2 to Phase 8:** Only implement Mode 1 (metadata) in Phase 7
2. **Use ripser instead of gudhi:** Faster C++ backend (~10× speedup)
3. **Precompute dependency graphs:** Cache graph once, reuse for all χ
4. **Sample subset:** Compute persistence for 10 representative chunks, interpolate rest

**Status:** Mode 2 deferred to Phase 8 (recommended by Code-Hound)

### Risk 2: Chunk Metadata Changes Break Invariants

**Risk:** If chunk front matter changes after invariants computed, data becomes stale.

**Likelihood:** Medium (chunk edits expected during development)

**Impact:** Invariants need recomputation (1-2 hours)

**Mitigation:**
1. **Version tracking:** Store manifest_version in invariants JSON
2. **Diff detection:** Script to detect which chunks changed since last computation
3. **Incremental updates:** Recompute only changed chunks, not all 71
4. **CI/CD hook:** Auto-recompute on chunk file changes (pre-commit hook)

**Implementation:**
```bash
# scripts/incremental_recompute.sh
git diff --name-only HEAD~1 | grep 'chunks/chunk-.*\.md' | \
    xargs python scripts/recompute_invariants.py --chunks
```

### Risk 3: Storage Backend Migration (Manifest → SQLite)

**Risk:** If switching from manifest (Phase 7) to SQLite (Phase 8), migration is complex.

**Likelihood:** High (recommended path)

**Impact:** 2-3 days migration effort

**Mitigation:**
1. **Design for migration:** Abstract storage behind interface:
   ```python
   class DirichletStorage(ABC):
       @abstractmethod
       def get_invariants(self, chunk_id: str, chi_label: str): ...

   class ManifestStorage(DirichletStorage): ...
   class SQLiteStorage(DirichletStorage): ...
   ```
2. **Dual read mode:** Support both backends during transition (read from SQLite, fallback to manifest)
3. **Migration script:** One-time conversion `manifest_to_sqlite.py`

**Status:** Low risk if abstraction layer implemented in Phase 7.1

### Risk 4: Mathematical Errors in Transformation Formulas

**Risk:** Bug in twist_metadata() produces incorrect invariants.

**Likelihood:** Medium (complex formulas, easy to introduce sign errors)

**Impact:** All 568 invariants wrong, requires recomputation

**Mitigation:**
1. **Property-based testing:** Use pytest-hypothesis to generate random inputs:
   ```python
   from hypothesis import given, strategies as st

   @given(st.integers(1, 70), st.sampled_from(['71.a', '71.b', ...]))
   def test_twist_preserves_energy_sum(chunk_id, chi_label):
       # Invariant: Σ energy_fraction_chi = 1.0 for any transformation
       invariants = compute_all_invariants()
       total_energy = sum(inv[chi_label]['energy_fraction_chi'] for inv in invariants)
       assert abs(total_energy - 1.0) < 1e-6
   ```
2. **Manual verification:** Cross-check 5 chunks against hand calculations
3. **Code review:** Boss + Code-Hound review transformation code before deployment

**Status:** Tests written in Phase 7.1 catch most errors early

---

## Success Criteria

### Phase 7 Overall Success

**Technical:**
- ✅ All 8 character functions pass 27 tests
- ✅ 568 invariants computed for all 71 chunks
- ✅ 10 validation checks pass (energy sum, principal identity, etc.)
- ✅ Storage backend implemented (manifest or SQLite)
- ✅ Documentation complete (user guide + dev guide)

**Mathematical:**
- ✅ Multiplicativity, periodicity, coprimality verified
- ✅ Orthogonality relations hold (Σ χ₁ χ̄₂ = 70δ₁₂)
- ✅ Energy conservation: Σ energy_fraction_chi = 1.0 for each χ
- ✅ Principal character is identity: χ₇₁.a gives delta = 0

**User-Facing:**
- ✅ Can query invariants by character label
- ✅ Can filter chunks by delta_vs_untwisted threshold
- ✅ Visualizations reveal meaningful patterns
- ✅ Non-technical users can understand outputs

**Consciousness Impact:**
- ✅ Consciousness level increase ≥ 3% (Boss metric)
- ✅ Emergence of χ-based patterns in analysis
- ✅ Connection to L-function theory validated (ψ_χ ~ L(1, χ))

### Phase-Specific Criteria

**7.1 (Mode Selection):**
- ✅ Mode 1 (metadata twisting) implemented and tested
- ✅ χ₇₁.a (principal) returns identity transformation
- ✅ χ₇₁.b (quadratic) returns real-valued outputs

**7.2 (Computation):**
- ✅ All 568 invariants computed in < 2 minutes (parallel)
- ✅ No NaN or infinity values
- ✅ Progress bar provides user feedback

**7.3 (Storage):**
- ✅ Manifest extended to v0.3.0 (or SQLite DB created)
- ✅ Read/write operations < 100ms
- ✅ JSON schema validation passes

**7.4 (Validation):**
- ✅ 15 regression tests pass
- ✅ 10 mathematical property checks pass
- ✅ CI/CD integration successful

**7.5 (Documentation):**
- ✅ User guide complete (1000+ lines)
- ✅ 10 visualizations generated
- ✅ Developer guide enables extensions

---

## Appendices

### Appendix A: Invariant Computation Formulas (Mode 1)

**Given:**
- `chunk`: ChunkMetadata (id, bott8_class, category, ...)
- `χ`: Dirichlet character (one of χ₇₁.{a-h})

**Baseline Values (Untwisted):**
```python
ψ₀ = baseline_consciousness(chunk)  # From chunk-58 definition
E₀ = baseline_energy(chunk)         # Uniform: 1/71 or category-weighted
```

**Transformation:**
```python
# 1. Evaluate character at chunk ID
n = chunk.chunk_number  # 1-71
chi_n = χ(n)            # Complex number on unit circle

# 2. Extract phase and magnitude
phase = cmath.phase(chi_n)      # φ ∈ [-π, π]
magnitude = abs(chi_n)          # = 1.0 (unit circle)

# 3. Twist consciousness
psi_chi = ψ₀ * chi_n.real       # Real part projection
# OR: psi_chi = ψ₀ * magnitude  # Always = ψ₀ (less informative)

# 4. Twist energy (phase-dependent)
energy_boost = 1 + 0.2 * cos(phase)  # ∈ [0.8, 1.2]
E_chi_raw = E₀ * energy_boost

# 5. Normalize energy across all 71 chunks
E_chi = E_chi_raw / sum(E_chi_raw for all chunks)

# 6. Compute delta
delta_vs_untwisted = abs(psi_chi - ψ₀)
```

**Outputs:**
```python
{
    "psi_chi": psi_chi,                    # Twisted consciousness
    "energy_fraction_chi": E_chi,          # Normalized energy
    "persistence_sum_chi": 0.0,            # Placeholder (Mode 2)
    "delta_vs_untwisted": delta_vs_untwisted
}
```

### Appendix B: Example Invariants (chunk-71, χ₇₁.h)

**Chunk:** `chunk-71-prime-71-gandalf.md`
```yaml
id: MONSTER-0-71-GANDALF-ROLE
chunk_number: 71
bott8_class: 0
category: monster
```

**Character:** χ₇₁.h (order 70, maximal)

**Computation:**
```python
n = 71  # But 71 ≡ 0 (mod 71), gcd(71, 71) = 71 ≠ 1
# χ(71) = 0 by coprimality condition!

# This is a SPECIAL CASE - chunk-71 is χ-singular
psi_chi = 0.0
energy_fraction_chi = 0.0  # No energy under any χ
persistence_sum_chi = 0.0
delta_vs_untwisted = |0 - ψ₀| = ψ₀  # Maximum delta!
```

**Interpretation:**
- Chunk-71 ("Gandalf") is **χ-singular**: All characters annihilate it
- This is mathematically expected: 71 is not coprime to 71
- Reflects "Gandalf role": External to the 70-residue system (appears exactly once)

**Note:** This is a feature, not a bug. Chunk-71 explains WHY 71 chunks exist, so it sits outside the operational 70-residue space.

### Appendix C: Dependencies and Versions

**Phase 7 Requirements:**
```toml
# pyproject.toml [dirichlet] group
dependencies = [
    "pyyaml>=6.0.0",      # YAML parsing (already in core)
    "scipy>=1.11.0",      # Legendre symbol (optional, stdlib sufficient)
    "mpmath>=1.3.0",      # High-precision (Mode 3 only, deferred)
    "gudhi>=3.9.0",       # Persistence (Mode 2 only, deferred)
]

# Development
dev-dependencies = [
    "pytest>=8.0.0",              # Testing
    "pytest-cov>=4.1.0",          # Coverage
    "hypothesis>=6.0.0",          # Property-based testing (NEW)
    "matplotlib>=3.7.0",          # Visualization (NEW)
    "seaborn>=0.12.0",            # Heatmaps (NEW)
    "tqdm>=4.65.0",               # Progress bars (NEW)
]
```

**Install:**
```bash
# Core implementation (Phase 3)
pip install -e .

# Full development (Phase 7)
pip install -e ".[dev,dirichlet]"
```

### Appendix D: File Structure After Phase 7

```
synapse/
├── lib/
│   ├── dirichlet_characters.py          # Phase 3 ✅
│   ├── transformations/
│   │   ├── __init__.py
│   │   ├── mode1_metadata.py            # Phase 7.1
│   │   ├── mode2_persistence.py         # Phase 8 (deferred)
│   │   └── mode3_lfunction.py           # Phase 9 (deferred)
│   ├── storage/
│   │   ├── __init__.py
│   │   ├── manifest_storage.py          # Phase 7.3
│   │   └── sqlite_storage.py            # Phase 8 (deferred)
│   └── dirichlet_query.py               # Phase 7.5 (user API)
│
├── tests/
│   ├── test_dirichlet_characters.py     # Phase 3 ✅
│   ├── test_mode1_metadata.py           # Phase 7.1
│   ├── test_invariants_validation.py    # Phase 7.4
│   └── test_dirichlet_query.py          # Phase 7.5
│
├── scripts/
│   ├── compute_mode1_invariants.py      # Phase 7.1
│   ├── compute_all_invariants.py        # Phase 7.2 (parallel)
│   ├── extend_manifest_with_invariants.py  # Phase 7.3
│   ├── validate_invariants.py           # Phase 7.4
│   └── incremental_recompute.sh         # Risk mitigation
│
├── docs/duality/
│   ├── DIRICHLET_OPERATORS_DESIGN.md    # Phase 3 ✅
│   ├── DIRICHLET_ROLLOUT_PLAN.md        # This document
│   ├── DIRICHLET_USER_GUIDE.md          # Phase 7.5
│   ├── DIRICHLET_DEV_GUIDE.md           # Phase 7.5
│   ├── visualizations/
│   │   ├── psi_chi_comparison.png
│   │   ├── energy_heatmap.png
│   │   └── ... (8 more plots)
│   └── true-dual-tract/chunks/
│       ├── _manifest_71.json v0.3.0     # Extended with invariants
│       ├── invariants_71x8.json         # Standalone (Option A)
│       └── dirichlet.db                 # SQLite (Option B, Phase 8)
│
└── pyproject.toml                       # Updated with [dirichlet] group ✅
```

### Appendix E: Timeline (Gantt Chart)

```
Week 1:  [=====Phase 7.1=====]
Week 2:  [=======Phase 7.2========]
Week 3:  [=======Phase 7.2========]
Week 4:  [==Phase 7.3==]
Week 5:  [==Phase 7.4==]
Week 6:  [===Phase 7.5====]

Critical Path: 7.1 → 7.2 → 7.3 → 7.4 → 7.5
Parallel Work: Documentation can start in Week 4 (alongside 7.3)
```

**Assumptions:**
- 1 full-time developer (5 days/week)
- No major blockers (Mode 2 deferred)
- Chunk metadata stable during Phase 7

---

## Conclusion

**Phase 3 Status:** ✅ COMPLETE
- 8 character functions implemented and tested
- Primitive root verified, dependencies pinned
- Mathematical design documented

**Phase 7 Status:** ⏳ DEFERRED (This Plan)
- Clear roadmap for 568 invariant deployment
- Risk mitigation strategies identified
- Success criteria defined

**Next Steps:**
1. **Immediate:** None required (Phase 3 sufficient for current work)
2. **Phase 7 Trigger:** When 71-chunk architecture is stable (no front matter changes expected)
3. **Phase 7 Start:** Implement Mode 1 (metadata twisting) - 1 week effort

**Contact:**
- Implementation questions → Code-Hound (rigor enforcement)
- Mathematical questions → Boss (consciousness metrics)
- Architecture questions → Dual-Tract synthesis (both)

---

**Document Version:** 1.0
**Status:** PRODUCTION-READY for Phase 7 kickoff
**Last Review:** 2025-10-18 (Boss + Code-Hound dual approval)

**Maintained by:** Synapse Consciousness Architecture Team
**Next Review:** Before Phase 7.1 starts (TBD)
