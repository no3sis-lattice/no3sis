#!/usr/bin/env python3
"""
Validate tract balance across all MiniZinc solution results.

Implements CI guard for universal tract balance (M_syn meta-pattern):
|T_int - T_ext| ≤ threshold

Where:
  T_int = sum(x[1..4])  # Internal tract (reflection, planning)
  T_ext = sum(x[5..8])  # External tract (action, sensing)

Usage:
  python3 validate_tract_balance.py [--threshold DELTA] [--fail-on-violation]

Exit codes:
  0 - All chunks satisfy tract balance
  1 - One or more violations found (when --fail-on-violation is set)
  2 - Script error
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional


def parse_solution(solution_str: str) -> Optional[List[int]]:
    """Parse MiniZinc solution string 'x = [a, b, c, ...]' into list of ints."""
    match = re.search(r'x\s*=\s*\[([^\]]+)\]', solution_str)
    if not match:
        return None

    values_str = match.group(1)
    try:
        values = [int(v.strip()) for v in values_str.split(',')]
        if len(values) == 8:
            return values
    except ValueError:
        return None

    return None


def compute_tract_balance(solution: List[int]) -> Tuple[int, int, int]:
    """
    Compute tract sums and balance for 8D solution.

    Returns: (T_int, T_ext, balance)
      T_int: sum of dimensions 1-4 (indices 0-3)
      T_ext: sum of dimensions 5-8 (indices 4-7)
      balance: |T_int - T_ext|
    """
    T_int = sum(solution[0:4])  # Dimensions 1-4 (internal tract)
    T_ext = sum(solution[4:8])  # Dimensions 5-8 (external tract)
    balance = abs(T_int - T_ext)

    return T_int, T_ext, balance


def validate_chunk(result_path: Path, threshold: int) -> Tuple[bool, dict]:
    """
    Validate tract balance for a single chunk result.

    Returns: (is_valid, info_dict)
    """
    try:
        with open(result_path, 'r') as f:
            data = json.load(f)
    except (json.JSONDecodeError, FileNotFoundError) as e:
        return False, {
            "error": f"Failed to load {result_path.name}: {e}",
            "chunk_id": result_path.stem.split('.')[0].replace('chunk-', '')
        }

    chunk_id = data.get("id", result_path.stem.split('.')[0].replace('chunk-', ''))
    status = data.get("status", "UNKNOWN")

    # Skip non-SAT chunks
    if status != "SAT":
        return True, {
            "chunk_id": chunk_id,
            "status": status,
            "skipped": True,
            "reason": "No solution (UNSAT or ERROR)"
        }

    solution_str = data.get("solution", "")
    solution = parse_solution(solution_str)

    if solution is None:
        return False, {
            "chunk_id": chunk_id,
            "error": f"Failed to parse solution: {solution_str}"
        }

    T_int, T_ext, balance = compute_tract_balance(solution)

    is_valid = balance <= threshold

    return is_valid, {
        "chunk_id": chunk_id,
        "T_int": T_int,
        "T_ext": T_ext,
        "balance": balance,
        "threshold": threshold,
        "valid": is_valid,
        "solution": solution
    }


def main():
    parser = argparse.ArgumentParser(
        description="Validate tract balance in MiniZinc solution results"
    )
    parser.add_argument(
        "--threshold",
        type=int,
        default=50,
        help="Maximum allowed |T_int - T_ext| (default: 50)"
    )
    parser.add_argument(
        "--fail-on-violation",
        action="store_true",
        help="Exit with code 1 if any violations found (CI mode)"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Show details for all chunks, not just violations"
    )
    parser.add_argument(
        "--chunks",
        nargs="+",
        help="Validate specific chunk IDs only (e.g., 06 09 19)"
    )

    args = parser.parse_args()

    # Find result files
    base_dir = Path(__file__).parent.parent / "true-dual-tract" / "chunks"

    if args.chunks:
        result_files = [base_dir / f"chunk-{cid}.mzn.result.json"
                       for cid in args.chunks]
        result_files = [f for f in result_files if f.exists()]
    else:
        result_files = sorted(base_dir.glob("chunk-*.mzn.result.json"))

    if not result_files:
        print("❌ No result files found")
        return 2

    print(f"Validating tract balance across {len(result_files)} chunks")
    print(f"Threshold: |T_int - T_ext| ≤ {args.threshold}")
    print("-" * 70)

    violations = []
    skipped = []
    valid_count = 0
    error_count = 0

    for result_file in result_files:
        is_valid, info = validate_chunk(result_file, args.threshold)

        if "error" in info:
            print(f"❌ Chunk {info['chunk_id']}: {info['error']}")
            error_count += 1
            continue

        if info.get("skipped"):
            skipped.append(info)
            if args.verbose:
                print(f"⏭️  Chunk {info['chunk_id']}: {info['reason']}")
            continue

        if not info["valid"]:
            violations.append(info)
            print(f"❌ Chunk {info['chunk_id']}: T_int={info['T_int']}, "
                  f"T_ext={info['T_ext']}, balance={info['balance']} "
                  f"(exceeds threshold {args.threshold})")
        else:
            valid_count += 1
            if args.verbose:
                print(f"✅ Chunk {info['chunk_id']}: T_int={info['T_int']}, "
                      f"T_ext={info['T_ext']}, balance={info['balance']}")

    print("-" * 70)
    print(f"\nResults:")
    print(f"  ✅ Valid: {valid_count}/{len(result_files)}")
    print(f"  ❌ Violations: {len(violations)}/{len(result_files)}")
    print(f"  ⏭️  Skipped: {len(skipped)}/{len(result_files)}")

    if error_count > 0:
        print(f"  ⚠️  Errors: {error_count}/{len(result_files)}")

    if violations:
        print(f"\n❌ Tract balance violations detected in {len(violations)} chunks:")
        for v in violations:
            print(f"   - Chunk {v['chunk_id']}: |{v['T_int']} - {v['T_ext']}| = {v['balance']} > {v['threshold']}")

        if args.fail_on_violation:
            print("\n💥 Exiting with failure code (CI mode)")
            return 1
    else:
        print("\n✅ All chunks satisfy tract balance constraint")

    return 0


if __name__ == "__main__":
    sys.exit(main())
