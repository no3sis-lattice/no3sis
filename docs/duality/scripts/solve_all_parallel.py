#!/usr/bin/env python3
"""
Solve all 62 MZN models in parallel and extract witnesses for Lean4 injection.
Phase 8 Update: Support excluding documentation/deferred chunks.
"""

import argparse
import subprocess
import json
import re
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from typing import Dict, List, Optional, Set, Tuple

# Paths
MZN_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")
OUTPUT_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/solutions")
OUTPUT_DIR.mkdir(exist_ok=True)

def solve_chunk(chunk_num: int, timeout: float = 5.0) -> Tuple[int, Dict]:
    """
    Solve a single MZN chunk and return witness data.

    Args:
        chunk_num: Chunk number (1-62)
        timeout: Solver timeout in seconds

    Returns:
        (chunk_num, {
            "status": "SAT" | "UNSAT" | "ERROR",
            "witness": [x1...x8],  # Only if SAT
            "error": str           # Only if ERROR
        })
    """
    mzn_file = MZN_DIR / f"chunk-{chunk_num:02d}.mzn"

    if not mzn_file.exists():
        return (chunk_num, {
            "status": "ERROR",
            "error": f"File not found: {mzn_file}"
        })

    try:
        # Run minizinc with timeout
        result = subprocess.run(
            ["minizinc", "--solver", "Gecode", str(mzn_file)],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        if result.returncode != 0:
            return (chunk_num, {
                "status": "ERROR",
                "error": f"Solver error: {result.stderr[:200]}"
            })

        # Parse solution
        output = result.stdout.strip()

        # Check for UNSAT
        if "=====UNSATISFIABLE=====" in output:
            return (chunk_num, {"status": "UNSAT"})

        # Extract witness: x = [v1, v2, ..., v8];
        match = re.search(r'x = \[([0-9, ]+)\];', output)
        if not match:
            return (chunk_num, {
                "status": "ERROR",
                "error": f"Could not parse solution: {output[:100]}"
            })

        # Parse values
        values_str = match.group(1)
        witness = [int(v.strip()) for v in values_str.split(',')]

        if len(witness) != 8:
            return (chunk_num, {
                "status": "ERROR",
                "error": f"Expected 8 values, got {len(witness)}: {witness}"
            })

        # Validate unitary constraint
        if sum(witness) != 100:
            return (chunk_num, {
                "status": "SAT",
                "witness": witness,
                "warning": f"sum(x) = {sum(witness)}, expected 100"
            })

        return (chunk_num, {
            "status": "SAT",
            "witness": witness,
            "sum": sum(witness)
        })

    except subprocess.TimeoutExpired:
        return (chunk_num, {
            "status": "ERROR",
            "error": f"Timeout ({timeout}s)"
        })
    except Exception as e:
        return (chunk_num, {
            "status": "ERROR",
            "error": f"Exception: {str(e)}"
        })


def main():
    """Solve MZN chunks in parallel with optional exclusions."""
    parser = argparse.ArgumentParser(
        description="Solve MZN chunks in parallel (Phase 8: exclude documentation chunks)"
    )
    parser.add_argument(
        "--exclude",
        type=str,
        default="",
        help="Comma-separated chunk IDs to exclude (e.g., '01,02,19')"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=4,
        help="Number of parallel workers (default: 4)"
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="Solver timeout per chunk in seconds (default: 120)"
    )
    parser.add_argument(
        "--output",
        type=str,
        default="solve_results.json",
        help="Output filename (default: solve_results.json)"
    )

    args = parser.parse_args()

    # Parse exclusions
    excluded: Set[int] = set()
    if args.exclude:
        excluded = {int(x.strip()) for x in args.exclude.split(",")}

    # Determine chunks to solve
    all_chunks = set(range(1, 63))
    chunks_to_solve = sorted(all_chunks - excluded)

    print("=" * 70)
    print("Phase 8: Solving MZN Models (Computational Chunks Only)")
    print("=" * 70)
    print(f"MZN directory:      {MZN_DIR}")
    print(f"Output directory:   {OUTPUT_DIR}")
    print(f"Total chunks:       62")
    print(f"Excluded:           {len(excluded)} ({sorted(excluded)})")
    print(f"To solve:           {len(chunks_to_solve)}")
    print(f"Parallel workers:   {args.workers}")
    print(f"Timeout per chunk:  {args.timeout}s")
    print()

    results = {}
    sat_count = 0
    unsat_count = 0
    error_count = 0

    # Solve in parallel
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(solve_chunk, chunk_num, args.timeout): chunk_num
            for chunk_num in chunks_to_solve
        }

        for future in as_completed(futures):
            chunk_num, result = future.result()
            results[chunk_num] = result

            # Print progress
            status = result["status"]
            if status == "SAT":
                sat_count += 1
                witness = result["witness"]
                print(f"✅ Chunk {chunk_num:02d}: SAT - {witness}")
            elif status == "UNSAT":
                unsat_count += 1
                print(f"❌ Chunk {chunk_num:02d}: UNSAT")
            else:  # ERROR
                error_count += 1
                error_msg = result.get("error", "Unknown error")[:60]
                print(f"⚠️  Chunk {chunk_num:02d}: ERROR - {error_msg}")

    print()
    print("=" * 70)
    print("RESULTS SUMMARY")
    print("=" * 70)
    total = len(chunks_to_solve)
    print(f"SAT (solved):    {sat_count}/{total} ({sat_count/total*100:.1f}%)")
    print(f"UNSAT:           {unsat_count}/{total}")
    print(f"ERROR:           {error_count}/{total}")
    print()

    # Save results
    output_file = OUTPUT_DIR / args.output
    with open(output_file, 'w') as f:
        json.dump({
            "metadata": {
                "total_chunks": 62,
                "excluded_chunks": sorted(excluded),
                "solved_chunks": sorted(chunks_to_solve),
                "timeout": args.timeout,
                "workers": args.workers
            },
            "results": results
        }, f, indent=2, sort_keys=True)

    print(f"Results saved to: {output_file}")

    # Save individual witness files for SAT chunks
    witness_count = 0
    for chunk_num, result in results.items():
        if result["status"] == "SAT" and "witness" in result:
            witness_file = OUTPUT_DIR / f"chunk{chunk_num:02d}_witness.json"
            with open(witness_file, 'w') as f:
                json.dump({
                    "chunk": chunk_num,
                    "witness": result["witness"],
                    "sum": result.get("sum", sum(result["witness"]))
                }, f, indent=2)
            witness_count += 1

    print(f"Individual witness files: {witness_count} saved to {OUTPUT_DIR}/")
    print()

    # Identify problems
    if unsat_count > 0:
        print("⚠️  UNSAT chunks (over-constrained):")
        for chunk_num in sorted(results.keys()):
            if results[chunk_num]["status"] == "UNSAT":
                print(f"    - Chunk {chunk_num:02d}")
        print()

    if error_count > 0:
        print("⚠️  ERROR chunks (need investigation):")
        for chunk_num in sorted(results.keys()):
            if results[chunk_num]["status"] == "ERROR":
                error = results[chunk_num].get("error", "Unknown")
                print(f"    - Chunk {chunk_num:02d}: {error[:60]}")
        print()

    print(f"✅ Phase 8 solving complete: {sat_count}/{total} witnesses ready")
    return sat_count


if __name__ == "__main__":
    sat_count = main()
    # Success if ≥80% SAT
    exit(0 if sat_count >= 44 else 1)  # 44/55 = 80%
