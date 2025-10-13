#!/usr/bin/env python3
"""Fix proof tactics in all chunks - use `decide` instead of complex omega."""

import re
from pathlib import Path

CHUNKS_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/formal/Duality/Chunks")

# Pattern to match the complex proof
OLD_PROOF_PATTERN = r'''theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  constructor
  · rfl  -- unitary
  · unfold domainConstraints
    constructor <;> try \(unfold dimensionFloor tractMinimum uniformityConstraint tractBalance; omega\)'''

NEW_PROOF = '''theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  decide'''

count = 0
for chunk_file in sorted(CHUNKS_DIR.glob("Chunk*.lean")):
    content = chunk_file.read_text()

    if OLD_PROOF_PATTERN in content:
        new_content = content.replace(OLD_PROOF_PATTERN, NEW_PROOF)
        chunk_file.write_text(new_content)
        count += 1
        print(f"✅ Fixed {chunk_file.name}")

print(f"\n✅ Updated {count} chunks to use 'decide' tactic")
