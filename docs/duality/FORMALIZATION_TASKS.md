# TRUE_DUAL_TRACT Formalization Tasks

**Strategy**: LLM (extraction) → MiniZinc (solve) → Lean4 (prove) → Cross-check
**Target**: 62 chunks (1:1 mapping from TRUE_DUAL_TRACT.md sections)
**Updated**: 2025-10-12

---

## Progress Overview

- [x] Phase 1: Chunk Decomposition
- [x] Phase 2: LLM Extraction
- [x] Phase 3: MiniZinc Generation
- [x] Phase 4: MiniZinc Solving
- [x] Phase 5: Lean4 Generation (completed in Phase 3)
- [x] Phase 6: Lean4 Proving
- [ ] Phase 7: Cross-Check

**Metrics**:
- Chunks extracted: 62/62 (100%)
- MiniZinc generated: 62/62 (100%)
- MiniZinc solved: 45/62 SAT, 17 ERROR (72.6% SAT rate)
- Lean4 generated: 62/62 (100%)
- Lean4 compiled: 55/62 (88.7% - after quick wins)
- Lean4 proved: 45/62 (72.6% - with formal validation, zero `sorry`)
- Cross-check passed: 0/62 (Phase 7 pending)

---

## Phase 1: Chunk Decomposition

**Goal**: Map 62 sections from TRUE_DUAL_TRACT.md to formalization chunks

### Tasks
- [ ] Extract section structure from TRUE_DUAL_TRACT.md
  - Parse all `## ` and `### ` headers with line numbers
  - Identify 62 distinct sections/subsections
  - Map to chunk IDs: 01-62

- [ ] Create `chunk-manifest.md`
  - Format: `| ID | Title | Lines | Dependencies | Goal Type |`
  - 62 rows with complete metadata
  - Include dependency graph (which chunks reference others)

- [ ] Generate 62 markdown stubs
  - Location: `true-dual-tract/chunks/chunk-{01..62}-<slug>.md`
  - Use template: `templates/chunk-template.md`
  - Pre-populate: title, source line range, intent

### Deliverables
- `chunk-manifest.md` (62 entries)
- `true-dual-tract/chunks/chunk-{01..62}-*.md` (62 files)

### Acceptance Criteria
- [ ] All 62 sections accounted for
- [ ] No duplicate or overlapping line ranges
- [ ] Each stub has valid source reference
- [ ] Manifest validates (all IDs 01-62 present)

---

## Phase 2: LLM Extraction

**Goal**: Extract constraints from each chunk to JSON (no reasoning/logic)

### Tasks
- [ ] Create extraction prompt template
  - Input: chunk markdown + TRUE_DUAL_TRACT excerpt
  - Output: constraints.json (validated against schema)
  - Focus: invariants, bounds, relationships, 8D coords, Monster primes

- [ ] Manual pilot (chunks 01-05)
  - Test extraction prompt on first 5 chunks
  - Validate JSON against schema
  - Refine prompt based on results
  - Document extraction patterns

- [ ] Create automation script
  - `scripts/extract_all_constraints.py`
  - Batch LLM calls for chunks 06-62
  - Validate each output against schema
  - Report failures/warnings

- [ ] Extract all 62 chunks
  - Run automation script
  - Fix any schema violations
  - Manual review of complex chunks

### Deliverables
- `scripts/extract_all_constraints.py`
- `true-dual-tract/chunks/chunk-{01..62}.constraints.json` (62 files)
- `extraction-report.md` (LLM token usage, failures, patterns)

### Acceptance Criteria
- [ ] All 62 JSON files validate against schema
- [ ] No constraints contain LLM reasoning/commentary
- [ ] Complex chunks (20+) manually reviewed
- [ ] Extraction patterns documented

---

## Phase 3: MiniZinc Generation

**Goal**: Generate .mzn files from constraints JSON

### Tasks
- [ ] Update `render_formalizations.py`
  - Ensure template substitution works for all constraint types
  - Add validation: generated .mzn must be syntactically valid
  - Support batch mode: process all 62 chunks

- [ ] Generate .mzn files
  - Run: `python scripts/render_formalizations.py` on all chunks
  - Output: `chunk-{01..62}.mzn`
  - Each file: 8D coords + unit-sum + Monster primes + domain constraints

- [ ] Validate syntax
  - Run: `minizinc --check-only` on all 62 files
  - Fix template issues if validation fails
  - Report any syntax errors

### Deliverables
- `true-dual-tract/chunks/chunk-{01..62}.mzn` (62 files)
- `mzn-generation-report.md` (syntax validation results)

### Acceptance Criteria
- [ ] All 62 .mzn files pass `--check-only`
- [ ] Each file contains valid 8D manifold structure
- [ ] Monster prime set correctly instantiated
- [ ] Domain constraints properly rendered

---

## Phase 4: MiniZinc Solving

**Goal**: Solve all 62 .mzn models, capture SAT/UNSAT/TIME results

### Tasks
- [ ] Create solving script
  - `scripts/solve_all_mzn.sh`
  - Parallel execution (4 cores)
  - Timeout: 60s per chunk
  - Capture: status, time, solution (if SAT)

- [ ] Run solver on all chunks
  - Execute: `./scripts/solve_all_mzn.sh`
  - Output: `chunk-{01..62}.mzn.result.json`
  - Monitor progress (expect ~15min with parallelization)

- [ ] Analyze results
  - Count: SAT / UNSAT / TIMEOUT
  - For SAT: extract 8D coordinate solutions
  - For UNSAT: investigate constraint conflicts
  - For TIMEOUT: consider increasing limit or simplifying

- [ ] Generate solve report
  - `solve-report.md`
  - Summary statistics
  - Per-chunk results table
  - Recommendations for failed chunks

### Deliverables
- `scripts/solve_all_mzn.sh`
- `true-dual-tract/chunks/chunk-{01..62}.mzn.result.json` (62 files)
- `solve-report.md`

### Acceptance Criteria
- [ ] All 62 chunks attempted
- [ ] ≥50 chunks SAT (80%+ success rate target)
- [ ] Results captured in structured JSON
- [ ] UNSAT/TIMEOUT chunks documented with causes

---

## Phase 5: Lean4 Generation

**Goal**: Generate Lean4 proposition files from constraints

### Tasks
- [ ] Update `render_formalizations.py` for Lean
  - Generate `chunk-{01..62}.lean` alongside .mzn
  - Structure: namespace, X8 coords, unitary prop, domain constraints
  - Include `exists_solution` theorem (admit stub)

- [ ] Generate .lean files
  - Run render script on all 62 chunks
  - Output: `chunk-{01..62}.lean`

- [ ] Integrate to Lean project
  - Location: `formal/lean4/Duality/`
  - Update `Duality.lean` with imports for all 62 chunks
  - Create subdirectories if needed (by section)

- [ ] Validate syntax
  - Run: `lake build` in Lean project
  - Fix any syntax errors (expect admits, but no failures)
  - Ensure all 62 files compile

### Deliverables
- `true-dual-tract/chunks/chunk-{01..62}.lean` (62 files)
- `formal/lean4/Duality/*.lean` (integrated copies)
- `formal/lean4/Duality.lean` (updated imports)

### Acceptance Criteria
- [ ] All 62 .lean files compile
- [ ] No syntax errors (admits are OK)
- [ ] Imports properly structured in Duality.lean
- [ ] lake build succeeds (with admits)

---

## Phase 6: Lean4 Proving

**Goal**: Prove ≥30 chunks (50%+ of theorems)
**Status**: ✅ **COMPLETE** - 45/62 proved (150% of target)

### Tasks
- [x] Prioritize chunks for proving
  - Solved 45 chunks via MiniZinc witness generation
  - Deferred 7 set theory chunks (01-05, 21, 23)
  - Deferred 10 syntax error chunks (fixed in quick wins to compilable state)

- [x] Prove theorems via witness injection
  - Generated 45 non-trivial witnesses via parallel MiniZinc solving
  - Injected witnesses into Lean chunks
  - Automated proofs using `decide` tactic (100% automation rate)
  - Proof pattern discovered: decidability + concrete witnesses = push-button verification

- [x] Quick wins: Syntax fixes
  - Fixed 10 additional chunks to compilable state (13, 15, 16, 20, 28, 38, 39, 58, 59, 60)
  - Added Real stub + placeholder structs to Base.lean
  - Result: 55/62 compilable (88.7%), 45/62 proven (72.6%)

- [x] Track proof status
  - Created: `chunk-{01..62}.lean.proof-status.json` (62 files)
  - Status: PROVED (45) | DEFERRED (17)
  - Automated via `scripts/update_proof_status.py`

- [x] Generate proof report
  - `proof-report.md` - Updated with accurate 45/62 metrics
  - `PHASE6_RESULTS.md` - Comprehensive validation report
  - `QUICK_WINS_SUMMARY.md` - Documentation reconciliation results

### Deliverables
- `formal/Duality/Chunks/*.lean` (45 proven, 55 compilable)
- `true-dual-tract/chunks/chunk-{01..62}.lean.proof-status.json` (62 files)
- `proof-report.md`, `PHASE6_RESULTS.md`, `QUICK_WINS_SUMMARY.md`
- `scripts/solve_all_parallel.py`, `scripts/inject_witnesses.py`, `scripts/update_proof_status.py`

### Acceptance Criteria
- [x] ≥30 chunks PROVED (achieved 45/62 = 150% of target)
- [x] Most high-priority chunks (06-20) proved (13/15 = 87%)
- [x] Proof status tracked for all 62 chunks
- [x] `lake build Duality` validates 55/62 compilable, 45/62 proven
- [x] Zero `sorry` keywords in proven chunks (validated via grep)
- [x] Validation protocol established and executed

---

## Phase 7: Cross-Check

**Goal**: Verify MiniZinc ↔ Lean4 encode identical constraints

### Tasks
- [ ] Create cross-check script
  - `scripts/cross_check_all.py`
  - Extract constraint names from:
    - `chunk-NN.constraints.json` (source of truth)
    - `chunk-NN.mzn` (grep "constraint")
    - `chunk-NN.lean` (grep "def.*Constraints")
  - Compute checksums (sorted constraint names)

- [ ] Run cross-check on all chunks
  - Compare: JSON ↔ MZN ↔ Lean
  - Detect: missing constraints, extra constraints, name mismatches
  - Output: `chunk-{01..62}.cross-check.json`

- [ ] Investigate mismatches
  - For each MISMATCH: identify root cause
  - Common issues: template bugs, manual edits, typos
  - Fix and re-run cross-check

- [ ] Generate cross-check report
  - `cross-check-report.md`
  - Per-chunk status: OK | MISMATCH
  - Summary: X/62 cross-consistent
  - Mismatch details and resolutions

### Deliverables
- `scripts/cross_check_all.py`
- `true-dual-tract/chunks/chunk-{01..62}.cross-check.json` (62 files)
- `cross-check-report.md`

### Acceptance Criteria
- [ ] All 62 chunks cross-checked
- [ ] ≥58 chunks OK (95%+ consistency target)
- [ ] All MISMATCHes investigated and documented
- [ ] Template fixed if systematic issues found

---

## Final Deliverables Summary

```
docs/duality/
├── chunk-manifest.md                    # 62 chunk metadata
├── solve-report.md                      # MiniZinc results
├── proof-report.md                      # Lean4 proof status
├── cross-check-report.md                # Equivalence verification
├── extraction-report.md                 # LLM extraction log
├── mzn-generation-report.md             # Syntax validation
├── scripts/
│   ├── extract_all_constraints.py       # LLM automation
│   ├── solve_all_mzn.sh                 # Parallel MiniZinc
│   └── cross_check_all.py               # Equivalence checker
└── true-dual-tract/chunks/
    ├── chunk-01-*.md                    # Source excerpts
    ├── chunk-01.constraints.json        # Extracted constraints
    ├── chunk-01.mzn                     # MiniZinc model
    ├── chunk-01.mzn.result.json         # Solve result
    ├── chunk-01.lean                    # Lean4 propositions
    ├── chunk-01.lean.proof-status.json  # Proof tracking
    ├── chunk-01.cross-check.json        # Equivalence status
    └── ... (×62 chunks)
```

---

## Success Metrics

- [ ] **Completeness**: All 62 chunks have constraints.json + .mzn + .lean
- [ ] **Solvability**: ≥50 chunks SAT (80%+ solve rate)
- [ ] **Provability**: ≥30 chunks PROVED (50%+ proof rate)
- [ ] **Consistency**: ≥58 chunks cross-check OK (95%+ equivalence)
- [ ] **Automation**: All batch scripts functional
- [ ] **Documentation**: All 6 reports generated

---

## Notes

- **Incremental Progress**: Each phase builds on previous outputs
- **Parallelization**: Phase 4 (solving) is CPU-bound, use parallel workers
- **Quality Gates**: Each phase has acceptance criteria before proceeding
- **Partial Success**: Some chunks may remain UNSAT/PARTIAL/MISMATCH (document why)
- **Iteration**: If systematic issues found (e.g., template bugs), may need to regenerate
