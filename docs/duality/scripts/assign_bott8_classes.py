#!/usr/bin/env python3
"""
Assign Bott[8] classes (0-7) to all 71 chunks.
Target distribution: [9,9,9,9,9,9,9,8]
"""
import json

# New chunks (63-71) already have Bott[8] assignments
new_chunks_bott8 = {
    "chunk-63": 0,  # BOTT8-BASIS-0-K-THEORY
    "chunk-64": 1,  # BOTT8-BASIS-1-VECTOR-BUNDLES
    "chunk-65": 2,  # BOTT8-BASIS-2-CLIFFORD-ALGEBRAS
    "chunk-66": 3,  # BOTT8-BASIS-3-STABLE-HOMOTOPY
    "chunk-67": 4,  # BOTT8-BASIS-4-RIEMANN-MANIFOLD
    "chunk-68": 5,  # BOTT8-BASIS-5-FIBER-BUNDLES
    "chunk-69": 6,  # BOTT8-BASIS-6-CHARACTERISTIC-CLASSES
    "chunk-70": 7,  # BOTT8-BASIS-7-INDEX-THEOREM
    "chunk-71": 0,  # MONSTER-0-71-GANDALF-ROLE
}

# Count current assignments
class_counts = [0] * 8
for bott8_class in new_chunks_bott8.values():
    class_counts[bott8_class] += 1

print("Initial Bott[8] distribution (9 new chunks):")
print(f"  {class_counts}")

# Target distribution
target = [9, 9, 9, 9, 9, 9, 9, 8]

# Calculate remaining slots
remaining_slots = [target[i] - class_counts[i] for i in range(8)]
print(f"\nRemaining slots needed: {remaining_slots}")
print(f"Total remaining: {sum(remaining_slots)} (should be 62)")

assert sum(remaining_slots) == 62, f"Remaining slots: {sum(remaining_slots)}, expected 62"

# Existing 62 chunks (chunk-01 through chunk-62)
existing_chunks = [f"chunk-{i:02d}" for i in range(1, 63)]

# Round-robin assignment to fill deficits
bott8_assignments = {}

# Create priority queue: classes with largest deficits first
deficit_order = sorted(range(8), key=lambda i: remaining_slots[i], reverse=True)

chunk_idx = 0
for bott8_class in deficit_order:
    slots_needed = remaining_slots[bott8_class]
    for _ in range(slots_needed):
        if chunk_idx < len(existing_chunks):
            chunk_id = existing_chunks[chunk_idx]
            bott8_assignments[chunk_id] = bott8_class
            chunk_idx += 1

# Verify all 62 chunks assigned
assert len(bott8_assignments) == 62, f"Assigned: {len(bott8_assignments)}, expected 62"

# Combine with new chunks
all_bott8_assignments = {**bott8_assignments, **new_chunks_bott8}

# Validate final distribution
final_counts = [0] * 8
for bott8_class in all_bott8_assignments.values():
    final_counts[bott8_class] += 1

print(f"\nFinal Bott[8] distribution (all 71 chunks):")
print(f"  {final_counts}")
print(f"  Target: {target}")

assert final_counts == target, f"Final distribution {final_counts} doesn't match target {target}"
assert len(all_bott8_assignments) == 71, f"Total chunks: {len(all_bott8_assignments)}, expected 71"

# Output as JSON
output_file = "/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks/_bott8_assignments.json"
with open(output_file, "w") as f:
    json.dump(all_bott8_assignments, f, indent=2, sort_keys=True)

print(f"\n✓ Bott[8] assignments written to: {output_file}")
print(f"\nDistribution:")
for i in range(8):
    count = final_counts[i]
    chunks_in_class = [k for k, v in all_bott8_assignments.items() if v == i]
    print(f"  Class {i}: {count}/{ target[i]} chunks")
    print(f"    New: {[k for k in chunks_in_class if k in new_chunks_bott8]}")
    print(f"    Existing: {len([k for k in chunks_in_class if k not in new_chunks_bott8])} chunks")
