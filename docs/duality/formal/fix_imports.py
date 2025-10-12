#!/usr/bin/env python3
"""Update imports to include Mathlib.Tactic for the 'use' tactic."""

from pathlib import Path

chunks_dir = Path("Duality/Chunks")

fixed_count = 0

for chunk_file in sorted(chunks_dir.glob("Chunk*.lean")):
    content = chunk_file.read_text()

    if "import Mathlib.Data.Nat.Basic" in content and "import Mathlib.Tactic" not in content:
        # Add Mathlib.Tactic import
        new_content = content.replace(
            "import Mathlib.Data.Nat.Basic",
            "import Mathlib.Data.Nat.Basic\nimport Mathlib.Tactic"
        )

        chunk_file.write_text(new_content)
        fixed_count += 1
        print(f"Fixed: {chunk_file.name}")

print(f"\nTotal fixed: {fixed_count}/62 chunks")
