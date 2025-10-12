#!/usr/bin/env python3
"""
Identify which chunks compile successfully after X8 import fix.
Phase 5-Pre: Build baseline before lemma integration.
"""

import subprocess
import sys
from pathlib import Path
from typing import List, Tuple


def test_chunk_compilation(chunk_id: str, formal_dir: Path) -> Tuple[str, bool, str]:
    """Test if a single chunk compiles."""
    module_name = f"Duality.Chunks.Chunk{chunk_id}"

    try:
        result = subprocess.run(
            ["lake", "build", module_name],
            cwd=formal_dir,
            capture_output=True,
            text=True,
            timeout=30
        )

        success = result.returncode == 0
        error_msg = ""

        if not success:
            # Extract first error line
            for line in result.stderr.splitlines():
                if "error:" in line.lower():
                    error_msg = line.strip()
                    break

        return (chunk_id, success, error_msg)

    except subprocess.TimeoutExpired:
        return (chunk_id, False, "Compilation timeout")
    except Exception as e:
        return (chunk_id, False, f"Exception: {e}")


def main() -> int:
    base_dir = Path(__file__).resolve().parents[1]
    formal_dir = base_dir / "formal"

    if not formal_dir.exists():
        print(f"Error: Formal directory not found: {formal_dir}", file=sys.stderr)
        return 1

    # Test all 62 chunks
    chunk_ids = [f"{i:02d}" for i in range(1, 63)]

    print(f"Testing compilation of {len(chunk_ids)} chunks...")
    print("=" * 60)

    compilable = []
    failing = []

    for i, chunk_id in enumerate(chunk_ids, 1):
        cid, success, error = test_chunk_compilation(chunk_id, formal_dir)

        if success:
            print(f"✓ Chunk{cid}")
            compilable.append(cid)
        else:
            # Truncate error for display
            error_short = error[:80] if error else "Unknown error"
            print(f"✗ Chunk{cid}: {error_short}")
            failing.append((cid, error))

        # Progress indicator every 10 chunks
        if i % 10 == 0:
            print(f"  [{i}/{len(chunk_ids)} tested]")

    print("=" * 60)
    print(f"\nResults:")
    print(f"  Compilable: {len(compilable)}/62 ({100*len(compilable)/62:.1f}%)")
    print(f"  Failing: {len(failing)}/62 ({100*len(failing)/62:.1f}%)")

    if compilable:
        print(f"\nCompilable chunk range: {compilable[0]}-{compilable[-1]}")
        print(f"Compilable chunks: {', '.join(compilable[:20])}")
        if len(compilable) > 20:
            print(f"  ... and {len(compilable) - 20} more")

    if failing:
        print(f"\nFailing chunks (first 10):")
        for cid, error in failing[:10]:
            print(f"  {cid}: {error[:60]}")

    # Write results to file for Phase 5 use
    results_file = base_dir / "COMPILABLE_CHUNKS.txt"
    results_file.write_text("\n".join(compilable), encoding="utf-8")
    print(f"\nWrote compilable chunk list to: {results_file}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
