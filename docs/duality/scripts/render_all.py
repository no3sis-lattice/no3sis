#!/usr/bin/env python3
"""Batch render all 62 chunks"""
from pathlib import Path
import subprocess
import sys

chunks_dir = Path("true-dual-tract/chunks")
rendered = 0
skipped = 0
errors = 0

for i in range(1, 63):
    json_file = chunks_dir / f"chunk-{i:02d}.constraints.json"
    mzn_file = chunks_dir / f"chunk-{i:02d}.mzn"
    lean_file = chunks_dir / f"chunk-{i:02d}.lean"

    if not json_file.exists():
        print(f"ERROR: Missing {json_file}")
        errors += 1
        continue

    # Skip if already rendered
    if mzn_file.exists() and lean_file.exists():
        skipped += 1
        continue

    # Render
    try:
        result = subprocess.run(
            ["python3", "scripts/render_formalizations.py", str(json_file)],
            capture_output=True,
            text=True,
            check=True
        )
        if "Rendered" in result.stdout:
            rendered += 1
            print(f"✓ chunk-{i:02d}")
        else:
            print(f"? chunk-{i:02d} (unexpected output)")
            errors += 1
    except subprocess.CalledProcessError as e:
        print(f"✗ chunk-{i:02d}: {e}")
        errors += 1

print(f"\nSummary: {rendered} rendered, {skipped} skipped, {errors} errors")
sys.exit(1 if errors > 0 else 0)
