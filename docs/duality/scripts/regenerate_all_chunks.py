#!/usr/bin/env python3
"""
Phase 8: Regenerate all 62 chunks with improved transpilers.

Features:
- Uses --use-base-imports for consistent Lean generation
- Validates MZN syntax after generation (using --model-check-only)
- Tracks success/failure per chunk
- Generates detailed report
"""

import subprocess
import sys
from pathlib import Path
from typing import List, Tuple
import json


def regenerate_chunk(chunk_id: str, base_dir: Path, use_force: bool = False, validate_mzn: bool = True) -> Tuple[bool, str]:
    """Regenerate MZN and Lean for a single chunk."""

    json_path = base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id}.constraints.json"

    if not json_path.exists():
        return False, f"JSON not found: {json_path}"

    # Build command
    cmd = [
        "python3",
        "scripts/render_formalizations.py",
        str(json_path),
        "--use-base-imports"
    ]

    if use_force:
        cmd.append("--force")

    try:
        result = subprocess.run(
            cmd,
            cwd=base_dir,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode != 0:
            return False, f"Transpiler failed: {result.stderr[:200]}"

        # Validate MZN syntax (optional - can be slow)
        if validate_mzn:
            mzn_path = base_dir / "formal" / "Duality" / "Chunks" / f"Chunk{chunk_id}.mzn"
            if mzn_path.exists():
                validate_result = subprocess.run(
                    ["minizinc", "--model-check-only", str(mzn_path)],
                    capture_output=True,
                    text=True,
                    timeout=10
                )

                if validate_result.returncode != 0:
                    return False, f"MZN syntax error: {validate_result.stderr[:200]}"

        return True, "OK"

    except subprocess.TimeoutExpired:
        return False, "Timeout"
    except Exception as e:
        return False, f"Exception: {str(e)[:200]}"


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Regenerate all 62 chunks")
    parser.add_argument("--force", action="store_true",
                       help="Overwrite existing Lean files (default: preserve proofs)")
    parser.add_argument("--chunks", type=str,
                       help="Comma-separated list of chunk IDs (default: all 62)")
    parser.add_argument("--start", type=int, default=1,
                       help="Start chunk ID (default: 1)")
    parser.add_argument("--end", type=int, default=62,
                       help="End chunk ID (default: 62)")
    parser.add_argument("--no-validate", action="store_true",
                       help="Skip MZN syntax validation (faster)")
    parser.add_argument("--report", type=str, default="/tmp/phase8_regeneration.json",
                       help="Output report path")
    args = parser.parse_args()

    base_dir = Path.cwd()

    # Determine chunk list
    if args.chunks:
        chunk_ids = [cid.strip().zfill(2) for cid in args.chunks.split(",")]
    else:
        chunk_ids = [str(i).zfill(2) for i in range(args.start, args.end + 1)]

    print(f"Regenerating {len(chunk_ids)} chunks...")
    print(f"Force mode: {args.force}")
    print(f"MZN validation: {not args.no_validate}")
    print()

    results = {}
    success_count = 0
    failure_count = 0

    for i, chunk_id in enumerate(chunk_ids, 1):
        print(f"[{i:2d}/{len(chunk_ids):2d}] Chunk {chunk_id}...", end=" ", flush=True)

        success, message = regenerate_chunk(chunk_id, base_dir, args.force, validate_mzn=not args.no_validate)

        results[chunk_id] = {
            "success": success,
            "message": message
        }

        if success:
            success_count += 1
            print("OK")
        else:
            failure_count += 1
            print(f"FAIL: {message}")

    print()
    print("=" * 80)
    print(f"Regeneration complete: {success_count}/{len(chunk_ids)} successful")
    print(f"Failures: {failure_count}")
    print("=" * 80)

    # Write report
    report_path = Path(args.report)
    report_data = {
        "total_chunks": len(chunk_ids),
        "successful": success_count,
        "failed": failure_count,
        "force_mode": args.force,
        "mzn_validation": not args.no_validate,
        "results": results
    }

    report_path.write_text(json.dumps(report_data, indent=2))
    print(f"Report written to: {report_path}")

    # List failures
    if failure_count > 0:
        print()
        print("Failed chunks:")
        for chunk_id, result in results.items():
            if not result["success"]:
                print(f"  Chunk {chunk_id}: {result['message']}")

    return 0 if failure_count == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
