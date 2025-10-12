#!/usr/bin/env python3
"""Fix Lean 4.24 structure syntax in all chunk files."""

import re
from pathlib import Path

chunks_dir = Path("Duality/Chunks")

# Old structure definition pattern
old_pattern = r"structure X8 where\n  x1 x2 x3 x4 x5 x6 x7 x8 : Nat"

# New structure definition (Lean 4.24 compliant)
new_structure = """structure X8 where
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat
  x8 : Nat"""

fixed_count = 0

for chunk_file in sorted(chunks_dir.glob("Chunk*.lean")):
    content = chunk_file.read_text()

    if "x1 x2 x3 x4 x5 x6 x7 x8 : Nat" in content:
        # Replace the structure definition
        new_content = re.sub(
            r"structure X8 where\n  x1 x2 x3 x4 x5 x6 x7 x8 : Nat",
            new_structure,
            content
        )

        chunk_file.write_text(new_content)
        fixed_count += 1
        print(f"Fixed: {chunk_file.name}")

print(f"\nTotal fixed: {fixed_count}/62 chunks")
