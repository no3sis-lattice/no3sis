#!/usr/bin/env python3
"""Replace heavy Mathlib.Tactic import with lighter proof using core tactics."""

from pathlib import Path

chunks_dir = Path("Duality/Chunks")

# Simpler proof using only core Lean tactics
simple_proof = """theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x := by
  refine ⟨⟨100, 0, 0, 0, 0, 0, 0, 0⟩, ?_, ?_⟩
  · rfl
  · trivial"""

fixed_count = 0

for chunk_file in sorted(chunks_dir.glob("Chunk*.lean")):
    content = chunk_file.read_text()

    # Remove Mathlib.Tactic import
    if "import Mathlib.Tactic" in content:
        content = content.replace("\nimport Mathlib.Tactic", "")

    # Replace proof with simpler version
    if "theorem exists_solution" in content and ("use ⟨100" in content or "admit" in content):
        import re
        content = re.sub(
            r"theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x := by.*?(?=\n\nend Chunk)",
            simple_proof,
            content,
            flags=re.DOTALL
        )

        chunk_file.write_text(content)
        fixed_count += 1
        print(f"Simplified: {chunk_file.name}")

print(f"\nTotal simplified: {fixed_count}/62 chunks")
