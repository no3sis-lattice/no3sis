# Cross-Check Report

**Generated**: 2025-10-12
**Phase**: 7 (Cross-Check)

---

## Summary

```
✅ OK: 27/62 (43.5%)
⚠️  DEGENERATE: 5/62 (8.1%)
❌ MISMATCH: 30/62 (48.4%)
```

## Per-Chunk Analysis

| Chunk | JSON Total | MZN Active | MZN Unsupported | Lean Trivial | Status |
|-------|------------|------------|-----------------|--------------|--------|
| 01 | 13 | 1 | 15 | Yes | DEGENERATE |
| 02 | 8 | 1 | 10 | Yes | DEGENERATE |
| 03 | 19 | 1 | 21 | Yes | DEGENERATE |
| 04 | 16 | 1 | 18 | Yes | DEGENERATE |
| 05 | 27 | 1 | 29 | Yes | DEGENERATE |
| 06 | 3 | 3 | 4 | Yes | OK |
| 07 | 2 | 3 | 2 | Yes | MISMATCH |
| 08 | 3 | 3 | 4 | Yes | OK |
| 09 | 3 | 3 | 4 | Yes | OK |
| 10 | 2 | 3 | 2 | Yes | MISMATCH |
| 11 | 2 | 3 | 2 | Yes | MISMATCH |
| 12 | 3 | 3 | 3 | Yes | OK |
| 13 | 3 | 3 | 3 | Yes | OK |
| 14 | 2 | 3 | 2 | Yes | MISMATCH |
| 15 | 3 | 3 | 3 | Yes | OK |
| 16 | 3 | 3 | 3 | Yes | OK |
| 17 | 2 | 3 | 2 | Yes | MISMATCH |
| 18 | 3 | 3 | 4 | Yes | OK |
| 19 | 2 | 3 | 2 | Yes | MISMATCH |
| 20 | 3 | 3 | 3 | Yes | OK |
| 21 | 3 | 3 | 3 | Yes | OK |
| 22 | 2 | 3 | 2 | Yes | MISMATCH |
| 23 | 3 | 3 | 3 | Yes | OK |
| 24 | 2 | 3 | 2 | Yes | MISMATCH |
| 25 | 2 | 3 | 2 | Yes | MISMATCH |
| 26 | 2 | 3 | 2 | Yes | MISMATCH |
| 27 | 2 | 3 | 2 | Yes | MISMATCH |
| 28 | 3 | 3 | 3 | Yes | OK |
| 29 | 2 | 3 | 2 | Yes | MISMATCH |
| 30 | 3 | 3 | 4 | Yes | OK |
| 31 | 2 | 3 | 2 | Yes | MISMATCH |
| 32 | 2 | 3 | 2 | Yes | MISMATCH |
| 33 | 2 | 3 | 2 | Yes | MISMATCH |
| 34 | 2 | 3 | 2 | Yes | MISMATCH |
| 35 | 2 | 3 | 2 | Yes | MISMATCH |
| 36 | 2 | 3 | 2 | Yes | MISMATCH |
| 37 | 2 | 3 | 2 | Yes | MISMATCH |
| 38 | 3 | 3 | 3 | Yes | OK |
| 39 | 3 | 3 | 3 | Yes | OK |
| 40 | 2 | 3 | 2 | Yes | MISMATCH |
| 41 | 2 | 3 | 2 | Yes | MISMATCH |
| 42 | 2 | 3 | 2 | Yes | MISMATCH |
| 43 | 2 | 3 | 2 | Yes | MISMATCH |
| 44 | 2 | 3 | 2 | Yes | MISMATCH |
| 45 | 3 | 3 | 4 | Yes | OK |
| 46 | 2 | 3 | 2 | Yes | MISMATCH |
| 47 | 3 | 3 | 3 | Yes | OK |
| 48 | 3 | 3 | 4 | Yes | OK |
| 49 | 2 | 3 | 2 | Yes | MISMATCH |
| 50 | 2 | 3 | 2 | Yes | MISMATCH |
| 51 | 3 | 3 | 4 | Yes | OK |
| 52 | 3 | 3 | 4 | Yes | OK |
| 53 | 3 | 3 | 4 | Yes | OK |
| 54 | 3 | 3 | 3 | Yes | OK |
| 55 | 3 | 3 | 3 | Yes | OK |
| 56 | 3 | 3 | 3 | Yes | OK |
| 57 | 3 | 3 | 3 | Yes | OK |
| 58 | 3 | 3 | 3 | Yes | OK |
| 59 | 4 | 3 | 4 | Yes | MISMATCH |
| 60 | 4 | 3 | 4 | Yes | MISMATCH |
| 61 | 3 | 3 | 4 | Yes | OK |
| 62 | 2 | 3 | 2 | Yes | MISMATCH |

---

## Interpretation

**DEGENERATE Status**: Chunk has only unit-sum constraint active (all domain constraints marked UNSUPPORTED_SYNTAX).

**OK Status**: JSON constraint count matches MZN active constraints.

**MISMATCH Status**: Discrepancy between JSON and MZN constraint counts.

### Current State

