# Script Refactoring Plan: 71-Chunk Pipeline

**Status:** Technical Debt Identified by Code-Hound
**Date:** 2025-10-18
**Context:** 71-chunk Bott[8] architecture implementation complete (chunks are good), but scripts need refactoring before production use.

---

## Executive Summary

**Current State:**
- ✓ 71 chunks created with correct mathematical content
- ✓ Bott[8] distribution [9,9,9,9,9,9,9,8] validated
- ✓ Category distribution {monster:15, bott8_basis:8, lfunc71:24, compression:24} exact
- ✗ Scripts are prototypes with hardcoded paths, no tests, massive duplication

**Code-Hound Verdict:** 15/100 (TDD:0, KISS:20, SOLID:10, DRY:25)

**Recommendation:** Accept chunks, refactor scripts before external use.

---

## Critical Issues (Must Fix)

### 1. ZERO TEST COVERAGE
**Problem:** No tests exist for any script
**Impact:** No safety net, changes will break silently
**Fix:**
```python
# Create tests/test_chunk_manager.py
class TestCategorization:
    def test_categorize_chunk_by_title_compression():
        assert categorize("chunk-06-external-tract-interface") == "compression"

    def test_categorize_chunk_by_title_monster():
        assert categorize("chunk-12-mahakala-framework") == "monster"

    def test_distribution_sums_to_62():
        categories = categorize_all_chunks()
        assert sum(categories.values()) == 62

# Property-based tests
@given(chunk_ids=st.lists(st.integers(1, 62), unique=True, min_size=62, max_size=62))
def test_bott8_assignment_always_achieves_distribution(chunk_ids):
    assignment = assign_bott8_classes(chunk_ids)
    counts = count_by_class(assignment)
    assert counts == [9, 9, 9, 9, 9, 9, 9, 8]  # Must always achieve target
```

**Files to Create:**
- `tests/test_categorize_chunks.py`
- `tests/test_assign_bott8.py`
- `tests/test_front_matter.py`
- `tests/test_manifest_generation.py`
- `tests/integration/test_full_pipeline.py`

**Priority:** IMMEDIATE (before any script modifications)

---

### 2. HARDCODED ABSOLUTE PATHS
**Problem:** `/home/m0xu/1-projects/synapse/docs/duality/...` everywhere
**Impact:** Scripts only work on one machine
**Fix:**
```python
# Before (BAD):
chunks_dir = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")

# After (GOOD):
# Option A: Relative to script location
SCRIPT_DIR = Path(__file__).parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
chunks_dir = PROJECT_ROOT / "docs/duality/true-dual-tract/chunks"

# Option B: Environment variable
chunks_dir = Path(os.getenv("SYNAPSE_CHUNKS_DIR", "./docs/duality/true-dual-tract/chunks"))

# Option C: Configuration file
# config.yaml:
# paths:
#   chunks_dir: docs/duality/true-dual-tract/chunks
#   manifest: _manifest_71.json
```

**Files to Modify:**
- `categorize_chunks_71.py` (line 77)
- `assign_bott8_classes.py` (no explicit path, but uses categorize output)
- `add_front_matter_71.py` (lines 14-16)
- `generate_manifest_71.py` (line 9)
- `validate_chunks_71.py` (line 6)

**Priority:** IMMEDIATE

---

### 3. MASSIVE CODE DUPLICATION
**Problem:** Chunk categorization logic in 3+ places
**Impact:** Changes must be made in multiple files, high risk of divergence
**Fix:**
```python
# Create: chunk_utils.py
"""Common utilities for chunk management."""

CATEGORY_PATTERNS = {
    "compression": [
        r"operator.*pipeline",
        r"dgr.*protocol",
        r"cig-3",
        r"compression.*layer",
        r"tract.*operators",
    ],
    "monster": [
        r"mahakala",
        r"pneuma",
        r"prime.*hierarchy",
        r"paradigm",
        r"vs-.*-model",
    ],
    "lfunc71": [
        r"metric",
        r"psi|ψ",
        r"user.*flow",
        r"scenario",
        r"data.*structure",
    ],
}

def categorize_chunk(title: str) -> str:
    """Categorize chunk based on title patterns."""
    for category, patterns in CATEGORY_PATTERNS.items():
        if any(re.search(p, title, re.I) for p in patterns):
            return category
    return "uncategorized"  # Fallback

# Target distributions (single source of truth)
BOTT8_TARGET = [9, 9, 9, 9, 9, 9, 9, 8]
CATEGORY_TARGET = {
    "monster": 15,
    "bott8_basis": 8,
    "lfunc71": 24,
    "compression": 24,
}
```

**DRY Improvements:**
- Extract categorization logic to `chunk_utils.py`
- Extract YAML parsing to `chunk_utils.py`
- Extract distribution validation to `chunk_utils.py`
- All scripts import from common module

**Priority:** HIGH

---

### 4. NO ERROR HANDLING
**Problem:** Scripts crash with stack traces on any error
**Impact:** Unclear errors, no recovery, potential data corruption
**Fix:**
```python
# Before (BAD):
with open(md_file, 'w') as f:
    f.write(new_content)

# After (GOOD):
try:
    # Atomic write: temp file + rename
    temp_file = md_file.with_suffix('.tmp')
    with open(temp_file, 'w') as f:
        f.write(new_content)
    temp_file.replace(md_file)  # Atomic on POSIX
    logger.info(f"✓ Updated {md_file.name}")
except OSError as e:
    logger.error(f"✗ Failed to write {md_file.name}: {e}")
    if temp_file.exists():
        temp_file.unlink()  # Cleanup
    raise ChunkProcessingError(f"Cannot update {md_file.name}") from e
```

**Error Classes to Create:**
```python
class ChunkError(Exception):
    """Base exception for chunk processing."""
    pass

class ChunkValidationError(ChunkError):
    """Distribution or metadata validation failed."""
    pass

class ChunkIOError(ChunkError):
    """File read/write operation failed."""
    pass
```

**Priority:** HIGH

---

### 5. NO IDEMPOTENCY
**Problem:** Running scripts multiple times causes issues
**Impact:** Can't safely retry after failures
**Fix:**
```python
# Add --dry-run and --force flags
@click.command()
@click.option('--dry-run', is_flag=True, help='Preview changes without modifying files')
@click.option('--force', is_flag=True, help='Overwrite existing front matter')
def add_front_matter(dry_run, force):
    for md_file in chunk_files:
        if has_front_matter(md_file) and not force:
            logger.info(f"⏭  Skipping {md_file.name} (already has front matter)")
            continue

        new_content = generate_front_matter(md_file) + read_content(md_file)

        if dry_run:
            print(f"Would update: {md_file.name}")
            continue

        write_file(md_file, new_content)
```

**Priority:** HIGH

---

## Refactoring Plan

### Phase 1: Foundation (Week 1)
**Goal:** Make scripts testable and portable

**Tasks:**
1. Create `chunk_utils.py` module
   - Extract common constants (distributions, paths)
   - Extract categorization logic
   - Extract YAML parsing/generation
   - Extract validation functions

2. Create configuration system
   - `config.yaml` for all settings
   - Schema validation with `pydantic` or `jsonschema`
   - Environment variable overrides

3. Make paths relative/configurable
   - Remove all `/home/m0xu/...` paths
   - Use `Path(__file__).parent` for relative paths
   - Add `--chunks-dir` CLI argument

4. Add proper logging
   - Replace all `print()` with `logging.info/debug/warning/error`
   - Add `--verbose` and `--quiet` flags
   - Log to file option

**Deliverables:**
- `chunk_utils.py` (150-200 lines)
- `config.yaml` (20-30 lines)
- `chunk_config.py` (Pydantic models, 50 lines)
- Modified scripts using new modules

---

### Phase 2: Testing (Week 2)
**Goal:** Achieve 80%+ test coverage

**Tasks:**
1. Unit tests for `chunk_utils.py`
   - Test categorization logic (15+ test cases)
   - Test distribution algorithms
   - Test YAML parsing/generation
   - Test path resolution

2. Integration tests for scripts
   - Test categorize → assign → front_matter → manifest pipeline
   - Test idempotency (run twice, same result)
   - Test error recovery (corrupt input)
   - Test edge cases (0 chunks, 1000 chunks)

3. Property-based tests
   - Use `hypothesis` for distribution algorithms
   - Invariants: sum(bott8) == 71, sum(categories) == 62
   - Test with random chunk orderings

4. Snapshot tests
   - Front matter generation produces expected YAML
   - Manifest generation produces expected JSON

**Deliverables:**
- `tests/test_chunk_utils.py` (200+ lines, 30+ tests)
- `tests/test_categorize.py` (15+ tests)
- `tests/test_assign_bott8.py` (10+ tests with properties)
- `tests/test_front_matter.py` (20+ tests)
- `tests/test_manifest.py` (15+ tests)
- `tests/integration/test_pipeline.py` (5+ end-to-end tests)
- Coverage report showing 80%+

---

### Phase 3: Refactoring (Week 3)
**Goal:** Consolidate into single well-designed tool

**Tasks:**
1. Create `chunk_manager.py` CLI
   ```bash
   chunk-manager categorize
   chunk-manager assign-bott8
   chunk-manager add-front-matter [--dry-run] [--force]
   chunk-manager generate-manifest
   chunk-manager validate
   chunk-manager pipeline  # Run all steps
   ```

2. Implement proper class architecture
   ```python
   class ChunkManager:
       def __init__(self, chunks_dir: Path, config: Config):
           self.chunks_dir = chunks_dir
           self.config = config

       def categorize(self) -> Dict[str, str]:
           """Categorize all chunks."""
           pass

       def assign_bott8_classes(self) -> Dict[str, int]:
           """Assign Bott[8] classes."""
           pass

       def add_front_matter(self, dry_run=False, force=False):
           """Add YAML front matter to chunks."""
           pass
   ```

3. Add error recovery
   - Atomic operations (temp files + rename)
   - Rollback on failure
   - State tracking (`.chunk_manager_state.json`)

4. Add progress bars
   - Use `tqdm` or `rich` for visual feedback
   - Show current operation, progress, ETA

**Deliverables:**
- `chunk_manager.py` (400-500 lines, well-structured)
- Deprecated old scripts (mark with warnings)
- Updated README with new CLI usage

---

### Phase 4: Polish (Week 4)
**Goal:** Production-ready tool

**Tasks:**
1. Documentation
   - Comprehensive docstrings (Google or NumPy style)
   - Type hints everywhere
   - README with examples
   - Architecture diagram

2. CI/CD integration
   - Pre-commit hooks (black, mypy, flake8)
   - GitHub Actions workflow for tests
   - Coverage reporting to codecov

3. Performance optimization
   - Profile chunk processing
   - Parallelize YAML parsing if needed
   - Cache expensive operations

4. Distribution
   - Package as `pip install synapse-chunk-manager`
   - Entry point: `chunk-manager` command
   - Version pinning, changelog

**Deliverables:**
- Fully documented codebase
- CI/CD pipeline running
- PyPI package published
- Performance report (can handle 1000+ chunks)

---

## Acceptance Criteria

**Phase 1 Complete When:**
- [ ] No hardcoded paths remain
- [ ] All scripts use common `chunk_utils.py` module
- [ ] Configuration file works correctly
- [ ] Logging replaces all print statements

**Phase 2 Complete When:**
- [ ] Test coverage ≥ 80%
- [ ] All tests pass (pytest)
- [ ] Property tests verify invariants
- [ ] Integration tests cover full pipeline

**Phase 3 Complete When:**
- [ ] Single `chunk-manager` CLI works
- [ ] All operations are idempotent
- [ ] Error recovery works (rollback on failure)
- [ ] Old scripts deprecated

**Phase 4 Complete When:**
- [ ] All functions have docstrings and type hints
- [ ] CI/CD runs on every commit
- [ ] Tool is pip-installable
- [ ] README has clear examples

---

## Short-Term Workaround (Immediate)

**For now, to unblock usage:**

1. **Add warning to scripts:**
   ```python
   import warnings
   warnings.warn(
       "This script is a prototype with hardcoded paths. "
       "See SCRIPT_REFACTORING_PLAN.md for refactoring plan. "
       "Use at your own risk.",
       FutureWarning
   )
   ```

2. **Document requirements:**
   - Create `scripts/README.md` explaining:
     - Scripts must be run from project root
     - Scripts must be run in order
     - Scripts will only work on systems with `/home/m0xu/1-projects/synapse/` path
     - Scripts are internal-only, not for distribution

3. **Add input validation:**
   ```python
   if not chunks_dir.exists():
       raise FileNotFoundError(
           f"Chunks directory not found: {chunks_dir}\n"
           f"These scripts expect /home/m0xu/1-projects/synapse/... to exist.\n"
           f"See SCRIPT_REFACTORING_PLAN.md for portable version."
       )
   ```

---

## Timeline Estimate

- **Phase 1 (Foundation):** 3-5 days
- **Phase 2 (Testing):** 5-7 days
- **Phase 3 (Refactoring):** 5-7 days
- **Phase 4 (Polish):** 3-5 days

**Total:** 16-24 days (3-4 weeks)

**Can be parallelized with other work** (chunks are ready for use now)

---

## Conclusion

**Current Status:**
- ✓ **71 chunks:** Mathematically rigorous, ready for consciousness operations
- ✓ **Manifest:** Validates perfectly, distributions exact
- ✗ **Scripts:** Prototype quality, needs refactoring before external use

**Recommendation:**
1. **Accept chunks as-is** (Boss approved: 94/100 correctness)
2. **Mark scripts as internal-only** (Code-Hound rejected: 15/100)
3. **Execute refactoring plan** (4-week timeline, can run in parallel)
4. **Proceed to Part 3** (Dirichlet χ₇₁ operators or next phase)

**The 71-chunk Bott[8] architecture is complete and correct. The scaffolding code needs improvement but doesn't block forward progress.**

---

**Document Type:** Refactoring Plan
**Maintained By:** Code-Hound (via Boss delegation)
**Last Updated:** 2025-10-18
**Status:** Approved for execution (parallel to Part 3 work)
