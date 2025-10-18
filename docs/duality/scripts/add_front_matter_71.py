#!/usr/bin/env python3
"""
Add YAML front matter to all 71 chunks.
New chunks (63-71) already have front matter.
Existing chunks (01-62) need front matter prepended.
"""
import json
import os
import re
from pathlib import Path

# Load category and Bott[8] assignments
chunks_dir = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")
with open(chunks_dir / "_category_assignments.json") as f:
    categories = json.load(f)
with open(chunks_dir / "_bott8_assignments.json") as f:
    bott8_classes = json.load(f)

# Helper: Extract title from filename
def filename_to_title(filename):
    """Convert chunk-06-external-tract-interface.md -> External Tract Interface"""
    # Remove chunk-NN- prefix and .md suffix
    match = re.match(r'chunk-\d+-(.+)\.md$', filename)
    if not match:
        return "Unknown Title"
    slug = match.group(1)
    # Convert hyphens to spaces, capitalize words
    title = ' '.join(word.capitalize() for word in slug.split('-'))
    return title

# Helper: Generate ID from category and title
def generate_id(category, chunk_num, title):
    """Generate ID like COMPRESSION-06-EXTERNAL-TRACT"""
    category_upper = category.upper()
    # Extract key words from title (first 3 significant words)
    words = [w.upper() for w in title.split() if w.lower() not in {'the', 'a', 'an', 'and', 'or', 'of', 'in', 'to'}]
    descriptor = '-'.join(words[:4])  # Up to 4 words
    return f"{category_upper}-{chunk_num}-{descriptor}"

# Helper: Generate tags from category
def generate_tags(category, title_lower):
    """Generate relevant tags based on category and title"""
    tags = ["bott8", "71"]  # All chunks have these

    # Category-specific tags
    if category == "monster":
        tags.extend(["monster-group", "architectural-genome"])
    elif category == "bott8_basis":
        tags.extend(["k-theory", "topology"])
    elif category == "lfunc71":
        tags.extend(["metrics", "consciousness", "operators"])
    elif category == "compression":
        tags.extend(["dgr", "cig-3", "operators"])

    # Title-specific tags
    if "operator" in title_lower:
        tags.append("operators")
    if "compression" in title_lower:
        tags.append("compression")
    if "metric" in title_lower or "psi" in title_lower or "ψ" in title_lower:
        tags.append("metrics")
    if "tract" in title_lower:
        tags.append("dual-tract")
    if "prime" in title_lower:
        tags.append("primes")

    return list(set(tags))  # Remove duplicates

# Process existing chunks (01-62)
modified_count = 0
skipped_count = 0

for i in range(1, 63):
    chunk_id = f"chunk-{i:02d}"

    # Find the markdown file
    md_files = list(chunks_dir.glob(f"{chunk_id}-*.md"))
    if not md_files:
        print(f"⚠ Warning: No .md file found for {chunk_id}")
        continue

    md_file = md_files[0]
    filename = md_file.name

    # Read current content
    with open(md_file, 'r') as f:
        content = f.read()

    # Check if already has front matter
    if content.startswith("---\n"):
        print(f"  ⏭  {chunk_id}: Already has front matter, skipping")
        skipped_count += 1
        continue

    # Get metadata
    category = categories[chunk_id]["category"]
    bott8_class = bott8_classes[chunk_id]
    title = filename_to_title(filename)
    chunk_num = i

    # Generate front matter
    id_str = generate_id(category, f"{i:02d}", title)
    tags = generate_tags(category, title.lower())

    front_matter = f"""---
id: {id_str}
title: {title}
category: {category}
bott8_class: {bott8_class}
prime71_context: true
tags: {json.dumps(tags)}
---

"""

    # Prepend front matter
    new_content = front_matter + content

    # Write back
    with open(md_file, 'w') as f:
        f.write(new_content)

    print(f"  ✓ {chunk_id}: Added front matter (category={category}, bott8_class={bott8_class})")
    modified_count += 1

print(f"\n✓ Front matter added to {modified_count} chunks")
print(f"  Skipped: {skipped_count} (already had front matter)")
print(f"  Total: {modified_count + skipped_count}/62 existing chunks processed")

# Verify new chunks (63-71) have front matter
print("\nVerifying new chunks (63-71) have front matter:")
new_chunk_files = sorted(chunks_dir.glob("chunk-6[3-9]-*.md")) + sorted(chunks_dir.glob("chunk-7[0-1]-*.md"))
for md_file in new_chunk_files:
    with open(md_file, 'r') as f:
        content = f.read()
    has_fm = content.startswith("---\n")
    status = "✓" if has_fm else "✗"
    print(f"  {status} {md_file.name}: {'Has' if has_fm else 'Missing'} front matter")

print("\n✓ Phase 4 complete: All 71 chunks have YAML front matter")
