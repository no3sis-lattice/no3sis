# Cross-Check Report

Generated: 2025-10-12 07:56:31 UTC
Phase: 7 (Cross-Check)

---

## Summary

```
OK: 3/3 (100.0%)
DEGENERATE: 0/3 (0.0%)
MISMATCH: 0/3 (0.0%)
INSUFFICIENT: 0/3 (0.0%)
ERROR: 0/3 (0.0%)
```

## Per-Chunk Analysis

| Chunk | JSON Total | MZN Active | MZN Unsupported | Lean Trivial | Status | Checksums (J/M/L) |
|-------|------------|------------|-----------------|--------------|--------|-------------------|
| 06 | 5 | 6 | 0 | No | OK | 16c69d3a/16c69d3a/16c69d3a |
| 09 | 5 | 6 | 0 | No | OK | 18c628cb/18c628cb/18c628cb |
| 19 | 5 | 6 | 0 | No | OK | 3fdc7748/3fdc7748/3fdc7748 |

---

## Warnings

### Chunk 06
```
⚠  MZN annotation coverage: 5/6 (83%)
```

### Chunk 09
```
⚠  MZN annotation coverage: 5/6 (83%)
```

### Chunk 19
```
⚠  MZN annotation coverage: 5/6 (83%)
```


---

## Interpretation

DEGENERATE: Only the unit/structural constraint is active in MiniZinc.
OK: Name checksums match across modalities, or counts match if names are unavailable.
MISMATCH: Name checksums differ (preferred) or counts differ (fallback).
INSUFFICIENT: 2+ modalities have empty name sets (proper annotations required for parity check).