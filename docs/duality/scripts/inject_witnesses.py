#!/usr/bin/env python3
"""
Inject MZN witnesses into Lean4 chunks and uncomment proof theorems.
Phase 6 Track 2: Lean4 Witness Injection
Phase 8.5.1: Updated proof tactic to handle True clauses
"""

import json
import re
from pathlib import Path
from typing import List, Dict, Optional

# Paths
SOLUTIONS_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/solutions")
LEAN_DIR = Path("/home/m0xu/1-projects/synapse/docs/duality/formal/Duality/Chunks")
SOLVE_RESULTS = SOLUTIONS_DIR / "solve_results.json"

def load_solve_results() -> Dict:
    """Load MZN solve results."""
    with open(SOLVE_RESULTS) as f:
        return json.load(f)

def inject_witness_into_chunk(chunk_num: int, witness: List[int]) -> bool:
    """
    Inject witness into a Lean chunk file and uncomment theorems.

    Returns:
        True if successful, False if file doesn't exist or injection fails
    """
    lean_file = LEAN_DIR / f"Chunk{chunk_num:02d}.lean"

    if not lean_file.exists():
        print(f"⚠️  Chunk {chunk_num:02d}: Lean file not found: {lean_file}")
        return False

    # Read current content
    with open(lean_file, 'r') as f:
        content = f.read()

    # Check if already injected
    if f"def witness : X8 :=" in content and "?" not in content.split("def witness")[1].split("\n")[0]:
        print(f"⏭️  Chunk {chunk_num:02d}: Witness already injected, skipping")
        return True

    # Format witness values
    w1, w2, w3, w4, w5, w6, w7, w8 = witness

    # Pattern 1: Uncomment and inject witness definition
    # Replace: -- def witness : X8 := ⟨?, ?, ?, ?, ?, ?, ?, ?⟩
    # With:    def witness : X8 := ⟨91, 3, 3, 3, 0, 0, 0, 0⟩
    witness_pattern = r'-- def witness : X8 := ⟨\?, \?, \?, \?, \?, \?, \?, \?⟩'
    witness_replacement = f'def witness : X8 := ⟨{w1}, {w2}, {w3}, {w4}, {w5}, {w6}, {w7}, {w8}⟩'

    content_new = re.sub(witness_pattern, witness_replacement, content)

    if content_new == content:
        print(f"⚠️  Chunk {chunk_num:02d}: Could not find witness pattern to replace")
        return False

    # Pattern 2: Uncomment witness_valid theorem
    # PHASE 8.5.1: Updated proof tactic to handle True clauses
    # Replace: -- theorem witness_valid : unitary witness ∧ domainConstraints witness := by
    #          --   constructor
    #          --   · rfl  -- unitary
    #          --   · constructor <;> omega  -- domain constraints
    # With: (uncommented version with improved tactic)

    witness_valid_pattern = r'-- theorem witness_valid : unitary witness ∧ domainConstraints witness := by\n--   constructor\n--   · rfl  -- unitary\n--   · constructor <;> omega  -- domain constraints'
    witness_valid_replacement = '''theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  constructor
  · rfl  -- unitary
  · unfold domainConstraints
    repeat (first | trivial | decide | omega)'''

    content_new = re.sub(witness_valid_pattern, witness_valid_replacement, content_new)

    # Pattern 3: Uncomment exists_solution theorem
    # Replace: -- theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=
    #          --   ⟨witness, witness_valid⟩
    # With: (uncommented version)

    exists_pattern = r'-- theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=\n--   ⟨witness, witness_valid⟩'
    exists_replacement = '''theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=
  ⟨witness, witness_valid⟩'''

    content_new = re.sub(exists_pattern, exists_replacement, content_new)

    # Write updated content
    with open(lean_file, 'w') as f:
        f.write(content_new)

    print(f"✅ Chunk {chunk_num:02d}: Witness injected - {witness}")
    return True

def main():
    """Inject witnesses into all SAT chunks."""
    print("Phase 6 Track 2: Injecting witnesses into Lean4 chunks...")
    print(f"Solutions directory: {SOLUTIONS_DIR}")
    print(f"Lean directory: {LEAN_DIR}")
    print()

    # Load solve results
    results = load_solve_results()

    success_count = 0
    skip_count = 0
    fail_count = 0

    # Process each chunk
    for chunk_num_str, result in sorted(results.items(), key=lambda x: int(x[0])):
        chunk_num = int(chunk_num_str)

        if not result.get("sat") or "witness" not in result:
            continue  # Skip UNSAT/ERROR chunks

        witness = result["witness"]

        try:
            if inject_witness_into_chunk(chunk_num, witness):
                if "already injected" in str(chunk_num):
                    skip_count += 1
                else:
                    success_count += 1
            else:
                fail_count += 1
        except Exception as e:
            print(f"❌ Chunk {chunk_num:02d}: Exception - {str(e)}")
            fail_count += 1

    print()
    print("="*70)
    print("INJECTION SUMMARY")
    print("="*70)
    print(f"Injected:  {success_count}/45")
    print(f"Skipped:   {skip_count}/45 (already had witnesses)")
    print(f"Failed:    {fail_count}/45")
    print()

    if success_count >= 35:
        print(f"✅ Phase 6 Track 2 complete: {success_count} witnesses injected (target: 35+)")
    elif success_count >= 25:
        print(f"✅ Phase 6 Track 2 complete: {success_count} witnesses injected (minimum viable: 25)")
    else:
        print(f"⚠️  Phase 6 Track 2: {success_count} witnesses injected (below minimum viable: 25)")

    return success_count

if __name__ == "__main__":
    success_count = main()
    exit(0 if success_count >= 25 else 1)
