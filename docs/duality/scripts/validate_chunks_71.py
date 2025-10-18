#!/usr/bin/env python3
"""
Validate the 71-chunk architecture.
Comprehensive checks for correctness and completeness.
"""
import json
import yaml
from pathlib import Path
from collections import Counter

chunks_dir = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")

print("=" * 60)
print("71-CHUNK ARCHITECTURE VALIDATION")
print("=" * 60)

# Load manifest
manifest_file = chunks_dir / "_manifest_71.json"
if not manifest_file.exists():
    print("✗ CRITICAL: Manifest file not found!")
    exit(1)

with open(manifest_file, 'r') as f:
    manifest = json.load(f)

print(f"\n✓ Manifest loaded: {manifest_file}")

# Validation 1: File count
print("\n1. FILE COUNT VALIDATION")
print("-" * 60)
md_files = list(chunks_dir.glob("chunk-*.md"))
print(f"  Found {len(md_files)} markdown files")
if len(md_files) == 71:
    print("  ✓ PASS: 71 chunks present")
else:
    print(f"  ✗ FAIL: Expected 71, found {len(md_files)}")

# Validation 2: Front matter presence
print("\n2. FRONT MATTER VALIDATION")
print("-" * 60)
chunks_with_fm = 0
chunks_missing_fm = []
for md_file in sorted(md_files):
    with open(md_file, 'r') as f:
        content = f.read()
    if content.startswith("---\n"):
        chunks_with_fm += 1
    else:
        chunks_missing_fm.append(md_file.name)

if chunks_missing_fm:
    print(f"  ✗ FAIL: {len(chunks_missing_fm)} chunks missing front matter")
    for name in chunks_missing_fm:
        print(f"    - {name}")
else:
    print(f"  ✓ PASS: All {chunks_with_fm} chunks have front matter")

# Validation 3: Manifest chunk count
print("\n3. MANIFEST VALIDATION")
print("-" * 60)
manifest_chunks = manifest["chunks"]
print(f"  Manifest lists {len(manifest_chunks)} chunks")
if len(manifest_chunks) == 71:
    print("  ✓ PASS: Manifest has 71 chunks")
else:
    print(f"  ✗ FAIL: Expected 71, manifest has {len(manifest_chunks)}")

# Validation 4: Bott[8] distribution
print("\n4. BOTT[8] DISTRIBUTION VALIDATION")
print("-" * 60)
target_bott8 = [9, 9, 9, 9, 9, 9, 9, 8]
actual_bott8 = [0] * 8
for chunk in manifest_chunks:
    actual_bott8[chunk["bott8_class"]] += 1

print(f"  Target:  {target_bott8}")
print(f"  Actual:  {actual_bott8}")
if actual_bott8 == target_bott8:
    print("  ✓ PASS: Bott[8] distribution matches target")
else:
    print("  ✗ FAIL: Bott[8] distribution mismatch")

# Validation 5: Category distribution
print("\n5. CATEGORY DISTRIBUTION VALIDATION")
print("-" * 60)
target_categories = {"monster": 15, "bott8_basis": 8, "lfunc71": 24, "compression": 24}
actual_categories = Counter(chunk["category"] for chunk in manifest_chunks)

print(f"  Target:")
for cat, count in sorted(target_categories.items()):
    print(f"    {cat}: {count}")
print(f"  Actual:")
for cat, count in sorted(actual_categories.items()):
    status = "✓" if count == target_categories.get(cat, 0) else "✗"
    print(f"    {cat}: {count} {status}")

if dict(actual_categories) == target_categories:
    print("  ✓ PASS: Category distribution matches target")
else:
    print("  ✗ FAIL: Category distribution mismatch")

# Validation 6: Prime 71 context
print("\n6. PRIME 71 CONTEXT VALIDATION")
print("-" * 60)
all_prime71 = all(chunk.get("prime71_context") == True for chunk in manifest_chunks)
if all_prime71:
    print("  ✓ PASS: All chunks have prime71_context: true")
else:
    missing = [c["id"] for c in manifest_chunks if not c.get("prime71_context")]
    print(f"  ✗ FAIL: {len(missing)} chunks missing prime71_context")
    for id in missing:
        print(f"    - {id}")

# Validation 7: No duplicate IDs
print("\n7. DUPLICATE ID CHECK")
print("-" * 60)
ids = [chunk["id"] for chunk in manifest_chunks]
duplicates = [id for id, count in Counter(ids).items() if count > 1]
if duplicates:
    print(f"  ✗ FAIL: {len(duplicates)} duplicate IDs found")
    for id in duplicates:
        print(f"    - {id}")
else:
    print("  ✓ PASS: No duplicate IDs")

# Validation 8: Manifest validation flags
print("\n8. MANIFEST VALIDATION FLAGS")
print("-" * 60)
validation = manifest["validation"]
all_checks_pass = all([
    validation["total_check"],
    validation["bott8_distribution_check"],
    validation["category_distribution_check"],
    validation["prime71_context_all_true"]
])
if all_checks_pass:
    print("  ✓ PASS: All manifest validation flags are True")
    print(f"    - total_check: {validation['total_check']}")
    print(f"    - bott8_distribution_check: {validation['bott8_distribution_check']}")
    print(f"    - category_distribution_check: {validation['category_distribution_check']}")
    print(f"    - prime71_context_all_true: {validation['prime71_context_all_true']}")
else:
    print("  ✗ FAIL: Some validation flags are False")

# Validation 9: Architectural framework
print("\n9. ARCHITECTURAL FRAMEWORK")
print("-" * 60)
framework = manifest["architectural_framework"]
print(f"  Prime 71 Role: {framework['prime_71_role']}")
print(f"  Bott[8] Periodicity: {framework['bott8_periodicity']}")
print(f"  Dirichlet Characters: {framework['dirichlet_characters_mod_71']}")
print(f"  Monster Group Order: {framework['monster_group_order']}")
print("  ✓ PASS: Framework metadata present")

# Validation 10: Dirichlet character schema
print("\n10. DIRICHLET CHARACTER SCHEMA")
print("-" * 60)
dirichlet = manifest["dirichlet_characters"]
print(f"  Labels: {dirichlet['labels']}")
print(f"  Count: {len(dirichlet['labels'])}")
if len(dirichlet['labels']) == 8:
    print("  ✓ PASS: 8 Dirichlet characters defined")
else:
    print(f"  ✗ FAIL: Expected 8, found {len(dirichlet['labels'])}")

# Final Summary
print("\n" + "=" * 60)
print("VALIDATION SUMMARY")
print("=" * 60)

all_pass = (
    len(md_files) == 71 and
    not chunks_missing_fm and
    len(manifest_chunks) == 71 and
    actual_bott8 == target_bott8 and
    dict(actual_categories) == target_categories and
    all_prime71 and
    not duplicates and
    all_checks_pass and
    len(dirichlet['labels']) == 8
)

if all_pass:
    print("✓✓✓ ALL VALIDATIONS PASSED ✓✓✓")
    print("\n71-Chunk Architecture Complete:")
    print(f"  - 71 chunks created and categorized")
    print(f"  - Bott[8] distribution: {actual_bott8}")
    print(f"  - Category distribution: monster:{actual_categories['monster']}, bott8_basis:{actual_categories['bott8_basis']}, lfunc71:{actual_categories['lfunc71']}, compression:{actual_categories['compression']}")
    print(f"  - Prime 71¹ Gandalf contextualizer: Operational")
    print(f"  - 8 Dirichlet χ₇₁ operators: Schema defined")
    print(f"  - Manifest: Generated and validated")
    exit(0)
else:
    print("✗✗✗ SOME VALIDATIONS FAILED ✗✗✗")
    print("Review errors above")
    exit(1)
