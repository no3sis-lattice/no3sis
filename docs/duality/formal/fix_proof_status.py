#!/usr/bin/env python3
"""Remove misleading timing data from proof status files."""

import json
from pathlib import Path

chunks_dir = Path("../true-dual-tract/chunks")

fixed_count = 0

for status_file in sorted(chunks_dir.glob("chunk-*.lean.proof-status.json")):
    data = json.loads(status_file.read_text())

    # Remove fake timing field
    if "proof_time_ms" in data:
        del data["proof_time_ms"]

    # Add note about timing
    data["notes"] = (
        "Trivial proof using MiniZinc solution witness. "
        "domainConstraints = True. "
        "Build time not individually measured (part of parallel lake build)."
    )

    status_file.write_text(json.dumps(data, indent=2) + "\n")
    fixed_count += 1

    if fixed_count % 10 == 0:
        print(f"Fixed: {status_file.name}")

print(f"\n✓ Fixed {fixed_count}/62 proof status files")
print("✓ Removed misleading proof_time_ms field")
print("✓ Added accurate notes about build process")
