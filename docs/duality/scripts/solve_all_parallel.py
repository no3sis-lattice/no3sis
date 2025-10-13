#!/usr/bin/env python3
"""
Solve all 62 MZN models in parallel and extract witnesses for Lean4 injection.
Phase 6: Lean4 Proving
"""

import subprocess
import json
import re
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from typing import Dict, Optional, Tuple

# Paths
MZN_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")
OUTPUT_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/solutions")
OUTPUT_DIR.mkdir(exist_ok=True)

def solve_chunk(chunk_num: int) -> Tuple[int, Dict]:
    """
    Solve a single MZN chunk and return witness data.

    Returns:
        (chunk_num, {"witness": [x1...x8], "sat": bool, "time_ms": float, "error": Optional[str]})
    """
    mzn_file = MZN_DIR / f"chunk-{chunk_num:02d}.mzn"

    if not mzn_file.exists():
        return (chunk_num, {"sat": False, "error": f"File not found: {mzn_file}"})

    try:
        # Run minizinc with timeout
        result = subprocess.run(
            ["minizinc", "--solver", "Gecode", str(mzn_file)],
            capture_output=True,
            text=True,
            timeout=5.0  # 5 second timeout per chunk
        )

        if result.returncode != 0:
            return (chunk_num, {
                "sat": False,
                "error": f"Solver error: {result.stderr[:200]}"
            })

        # Parse solution
        output = result.stdout.strip()

        # Check for UNSAT
        if "=====UNSATISFIABLE=====" in output:
            return (chunk_num, {"sat": False, "unsat": True})

        # Extract witness: x = [v1, v2, ..., v8];
        match = re.search(r'x = \[([0-9, ]+)\];', output)
        if not match:
            return (chunk_num, {
                "sat": False,
                "error": f"Could not parse solution: {output[:100]}"
            })

        # Parse values
        values_str = match.group(1)
        witness = [int(v.strip()) for v in values_str.split(',')]

        if len(witness) != 8:
            return (chunk_num, {
                "sat": False,
                "error": f"Expected 8 values, got {len(witness)}: {witness}"
            })

        # Validate unitary constraint
        if sum(witness) != 100:
            return (chunk_num, {
                "sat": True,
                "witness": witness,
                "error": f"WARNING: sum(x) = {sum(witness)}, expected 100"
            })

        return (chunk_num, {
            "sat": True,
            "witness": witness,
            "sum": sum(witness)
        })

    except subprocess.TimeoutExpired:
        return (chunk_num, {"sat": False, "error": "Timeout (5s)"})
    except Exception as e:
        return (chunk_num, {"sat": False, "error": f"Exception: {str(e)}"})

def main():
    """Solve all 62 chunks in parallel."""
    print("Phase 6: Solving 62 MZN models in parallel...")
    print(f"MZN directory: {MZN_DIR}")
    print(f"Output directory: {OUTPUT_DIR}")
    print()

    results = {}
    sat_count = 0
    unsat_count = 0
    error_count = 0

    # Solve in parallel (4 workers)
    with ProcessPoolExecutor(max_workers=4) as executor:
        futures = {executor.submit(solve_chunk, i): i for i in range(1, 63)}

        for future in as_completed(futures):
            chunk_num, result = future.result()
            results[chunk_num] = result

            # Print progress
            if result.get("sat"):
                sat_count += 1
                witness = result["witness"]
                print(f"✅ Chunk {chunk_num:02d}: SAT - {witness}")
            elif result.get("unsat"):
                unsat_count += 1
                print(f"❌ Chunk {chunk_num:02d}: UNSAT")
            else:
                error_count += 1
                error_msg = result.get("error", "Unknown error")[:60]
                print(f"⚠️  Chunk {chunk_num:02d}: ERROR - {error_msg}")

    print()
    print("="*70)
    print("RESULTS SUMMARY")
    print("="*70)
    print(f"SAT (solved):    {sat_count}/62 ({sat_count/62*100:.1f}%)")
    print(f"UNSAT:           {unsat_count}/62")
    print(f"ERROR:           {error_count}/62")
    print()

    # Save results
    output_file = OUTPUT_DIR / "solve_results.json"
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2, sort_keys=True)

    print(f"Results saved to: {output_file}")

    # Save individual witness files for SAT chunks
    for chunk_num, result in results.items():
        if result.get("sat") and "witness" in result:
            witness_file = OUTPUT_DIR / f"chunk{chunk_num:02d}_witness.json"
            with open(witness_file, 'w') as f:
                json.dump({
                    "chunk": chunk_num,
                    "witness": result["witness"],
                    "sum": result["sum"]
                }, f, indent=2)

    print(f"Individual witness files saved to: {OUTPUT_DIR}/")
    print()

    # Identify problems
    if unsat_count > 0:
        print("UNSAT chunks (over-constrained):")
        for chunk_num in sorted(results.keys()):
            if results[chunk_num].get("unsat"):
                print(f"  - Chunk {chunk_num:02d}")
        print()

    if error_count > 0:
        print("ERROR chunks (need investigation):")
        for chunk_num in sorted(results.keys()):
            if not results[chunk_num].get("sat") and not results[chunk_num].get("unsat"):
                error = results[chunk_num].get("error", "Unknown")
                print(f"  - Chunk {chunk_num:02d}: {error[:50]}")
        print()

    print(f"✅ Phase 6 Track 1 complete: {sat_count}/62 witnesses ready for injection")
    return sat_count

if __name__ == "__main__":
    sat_count = main()
    exit(0 if sat_count >= 25 else 1)  # Exit 0 if we hit minimum viable target
