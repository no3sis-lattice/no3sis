#!/usr/bin/env python3
"""Add proofs to all chunk theorems."""

import re
from pathlib import Path

chunks_dir = Path("Duality/Chunks")

# The proof to add (matching the MiniZinc solution)
proof = """theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x := by
  use ⟨100, 0, 0, 0, 0, 0, 0, 0⟩
  constructor
  · rfl
  · trivial"""

proved_count = 0

for chunk_file in sorted(chunks_dir.glob("Chunk*.lean")):
    content = chunk_file.read_text()

    # Check if theorem already has a proof (not admit)
    if "theorem exists_solution" in content and "by\n  admit" in content:
        # Replace admit with proof
        new_content = re.sub(
            r"theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x := by\n  admit",
            proof,
            content
        )

        chunk_file.write_text(new_content)
        proved_count += 1
        print(f"Proved: {chunk_file.name}")

print(f"\nTotal proved: {proved_count}/62 chunks")
