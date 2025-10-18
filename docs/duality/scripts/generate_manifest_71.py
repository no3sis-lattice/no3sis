#!/usr/bin/env python3
"""
Generate _manifest_71.json from all 71 chunk front matter.
Includes validation, distributions, and Dirichlet character schema.
"""
import json
import yaml
import re
from pathlib import Path
from datetime import datetime

chunks_dir = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")
chunks = []

# Find all chunk markdown files
md_files = sorted(chunks_dir.glob("chunk-*.md"), key=lambda p: int(re.search(r'chunk-(\d+)', p.name).group(1)))

print(f"Found {len(md_files)} chunk files")

# Extract front matter from each chunk
for md_file in md_files:
    with open(md_file, 'r') as f:
        content = f.read()

    # Extract YAML front matter
    if not content.startswith("---\n"):
        print(f"⚠ Warning: {md_file.name} missing front matter")
        continue

    try:
        # Split on front matter delimiters
        parts = content.split("---\n", 2)
        if len(parts) < 3:
            print(f"⚠ Warning: {md_file.name} has malformed front matter")
            continue

        front_matter_str = parts[1]
        front_matter = yaml.safe_load(front_matter_str)

        # Add filename
        front_matter["filename"] = md_file.name

        chunks.append(front_matter)
        print(f"  ✓ Parsed: {md_file.name}")

    except yaml.YAMLError as e:
        print(f"⚠ Error parsing YAML in {md_file.name}: {e}")
        continue

print(f"\n✓ Parsed {len(chunks)} chunks successfully")

# Validate counts
assert len(chunks) == 71, f"Expected 71 chunks, found {len(chunks)}"

# Calculate distributions
bott8_counts = {i: 0 for i in range(8)}
category_counts = {"monster": 0, "bott8_basis": 0, "lfunc71": 0, "compression": 0}

for chunk in chunks:
    bott8_counts[chunk["bott8_class"]] += 1
    category_counts[chunk["category"]] += 1

# Validate distributions
target_bott8 = [9, 9, 9, 9, 9, 9, 9, 8]
target_categories = {"monster": 15, "bott8_basis": 8, "lfunc71": 24, "compression": 24}

print("\nDistribution Validation:")
print(f"  Bott[8]: {list(bott8_counts.values())}")
print(f"  Target:  {target_bott8}")
assert list(bott8_counts.values()) == target_bott8, "Bott[8] distribution mismatch"
print("  ✓ Bott[8] distribution matches target")

print(f"\n  Categories: {category_counts}")
print(f"  Target:     {target_categories}")
assert category_counts == target_categories, "Category distribution mismatch"
print("  ✓ Category distribution matches target")

# Verify all have prime71_context
all_prime71 = all(chunk.get("prime71_context") == True for chunk in chunks)
assert all_prime71, "Some chunks missing prime71_context: true"
print("  ✓ All chunks have prime71_context: true")

# Generate manifest
manifest = {
    "version": "0.1.0",
    "total_chunks": 71,
    "prime71_context": True,
    "architectural_framework": {
        "prime_71_role": "Gandalf contextualizer (largest sporadic prime, exponent 71¹)",
        "bott8_periodicity": "8-dimensional Riemann manifold foundation",
        "dirichlet_characters_mod_71": 8,
        "monster_group_order": "2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71"
    },
    "distributions": {
        "bott8_classes": {str(i): bott8_counts[i] for i in range(8)},
        "categories": category_counts
    },
    "dirichlet_characters": {
        "labels": ["71.a", "71.b", "71.c", "71.d", "71.e", "71.f", "71.g", "71.h"],
        "role": "operators_on_chunk_space",
        "materialization": "do_not_clone_chunks",
        "invariants_per_chunk": [
            "psi_chi",
            "energy_fraction_chi",
            "persistence_sum_chi",
            "delta_vs_untwisted"
        ],
        "note": "χ-invariants computed on demand, stored under chunk.invariants[chi_label]"
    },
    "chunks": chunks,
    "validation": {
        "total_check": len(chunks) == 71,
        "bott8_distribution_check": list(bott8_counts.values()) == target_bott8,
        "category_distribution_check": category_counts == target_categories,
        "prime71_context_all_true": all_prime71,
        "manifest_generated": datetime.utcnow().isoformat() + "Z"
    }
}

# Write manifest
output_file = chunks_dir / "_manifest_71.json"
with open(output_file, 'w') as f:
    json.dump(manifest, f, indent=2)

print(f"\n✓ Manifest written to: {output_file}")
print(f"\n Summary:")
print(f"  Total chunks: {len(chunks)}")
print(f"  Bott[8] distribution: {list(bott8_counts.values())}")
print(f"  Category distribution: {category_counts}")
print(f"  All validations: PASSED ✓")
print(f"\n✓ Phase 5 complete: Manifest generated and validated")
