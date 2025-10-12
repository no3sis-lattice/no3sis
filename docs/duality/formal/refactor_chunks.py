#!/usr/bin/env python3
"""Refactor all chunk files to use shared Base module."""

import re
from pathlib import Path

chunks_dir = Path("Duality/Chunks")

# Template for refactored chunk
CHUNK_TEMPLATE = """/-
{title}
-/

import Duality.Base

namespace {namespace}

open Duality

/-- Domain-specific constraints for this chunk -/
def domainConstraints : Prop :=
  True  -- {constraints_comment}

/-- Existence theorem: there exists a valid 8D configuration -/
theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints := by
  refine ⟨standardWitness, ?_, ?_⟩
  · exact standardWitness_unitary
  · trivial

end {namespace}
"""

refactored_count = 0
original_lines = 0
new_lines = 0

for chunk_file in sorted(chunks_dir.glob("Chunk*.lean")):
    content = chunk_file.read_text()
    original_lines += len(content.split('\n'))

    # Extract namespace
    namespace_match = re.search(r'namespace (Chunk\d+)', content)
    if not namespace_match:
        print(f"⚠ Skipped {chunk_file.name}: no namespace found")
        continue
    namespace = namespace_match.group(1)

    # Extract title from first comment
    title_match = re.search(r'/-\n(.+?)\n-/', content, re.DOTALL)
    title = title_match.group(1).strip() if title_match else "Template Lean4 spec"

    # Extract domainConstraints comment
    constraints_match = re.search(r'True  -- (.+)', content)
    constraints_comment = constraints_match.group(1) if constraints_match else "(no constraints)"

    # Generate refactored content
    new_content = CHUNK_TEMPLATE.format(
        title=title,
        namespace=namespace,
        constraints_comment=constraints_comment
    )

    chunk_file.write_text(new_content)
    new_lines += len(new_content.split('\n'))
    refactored_count += 1

    if refactored_count % 10 == 0:
        print(f"Refactored: {chunk_file.name}")

print(f"\n✓ Refactored {refactored_count}/62 chunks")
print(f"Lines reduced: {original_lines} → {new_lines} ({100 * (original_lines - new_lines) / original_lines:.1f}% reduction)")
