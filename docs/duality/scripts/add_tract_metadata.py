#!/usr/bin/env python3
"""
Add 'tract' metadata field to all 71 chunks.
Classification: internal | external | bridge | meta
"""
import yaml
import re
from pathlib import Path

chunks_dir = Path("/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks")

# Tract classification rules
def classify_tract(filename: str, title: str, category: str) -> str:
    """Classify chunk into tract based on title patterns and category."""
    title_lower = title.lower()
    filename_lower = filename.lower()

    # Meta tract: Bott8_basis and most monster chunks
    if category == "bott8_basis":
        return "meta"  # Topological foundations

    if category == "monster":
        # Exception: operational chunks are bridge/internal
        if "prime-hierarchy" in filename_lower or "self-modification" in filename_lower:
            return "internal"
        return "meta"  # Architectural/philosophical chunks

    # Explicit tract indicators in title
    if "external" in title_lower or "external-tract" in filename_lower:
        return "external"
    if "internal" in title_lower or "internal-tract" in filename_lower:
        return "internal"
    if "corpus-callosum" in filename_lower or "bridge" in title_lower:
        return "bridge"

    # Category-based defaults
    if category == "compression":
        # Compression chunks with operator pipelines
        if "external" in filename_lower:
            return "external"
        elif "internal" in filename_lower:
            return "internal"
        elif "corpus" in filename_lower or "bridge" in filename_lower:
            return "bridge"
        else:
            return "bridge"  # Default for compression: bridge (synthesis)

    if category == "lfunc71":
        # Metrics and consciousness are internal (self-reflective)
        if "metric" in title_lower or "psi" in title_lower or "ψ" in title_lower:
            return "internal"
        # User flows and scenarios are external (interface)
        if "user" in title_lower or "scenario" in title_lower or "flow" in title_lower:
            return "external"
        # Orchestration and data structures are bridge
        if "orchestration" in title_lower or "structure" in title_lower:
            return "bridge"
        # Default: internal (most lfunc71 are metrics)
        return "internal"

    # Fallback: meta
    return "meta"

# Process all chunks
chunks_updated = 0
chunks_skipped = 0

md_files = sorted(chunks_dir.glob("chunk-*.md"), key=lambda p: int(re.search(r'chunk-(\d+)', p.name).group(1)))

for md_file in md_files:
    with open(md_file, 'r') as f:
        content = f.read()

    # Extract front matter
    if not content.startswith("---\n"):
        print(f"⚠ Warning: {md_file.name} has no front matter, skipping")
        chunks_skipped += 1
        continue

    try:
        parts = content.split("---\n", 2)
        if len(parts) < 3:
            print(f"⚠ Warning: {md_file.name} has malformed front matter, skipping")
            chunks_skipped += 1
            continue

        front_matter_str = parts[1]
        body = parts[2]

        # Parse YAML
        front_matter = yaml.safe_load(front_matter_str)

        # Check if tract already exists
        if "tract" in front_matter:
            print(f"  ⏭  {md_file.name}: Already has tract field, skipping")
            chunks_skipped += 1
            continue

        # Classify tract
        filename = md_file.name
        title = front_matter.get("title", "")
        category = front_matter.get("category", "")

        tract = classify_tract(filename, title, category)

        # Add tract field
        front_matter["tract"] = tract

        # Regenerate YAML (preserve order: id, title, category, bott8_class, tract, prime71_context, tags)
        ordered_fm = {}
        for key in ["id", "title", "category", "bott8_class", "tract", "prime71_context", "tags"]:
            if key in front_matter:
                ordered_fm[key] = front_matter[key]

        # Add any remaining keys
        for key, value in front_matter.items():
            if key not in ordered_fm:
                ordered_fm[key] = value

        # Write back
        new_front_matter_str = yaml.dump(ordered_fm, default_flow_style=False, sort_keys=False)
        new_content = f"---\n{new_front_matter_str}---\n\n{body}"

        with open(md_file, 'w') as f:
            f.write(new_content)

        print(f"  ✓ {md_file.name}: Added tract={tract} (category={category})")
        chunks_updated += 1

    except yaml.YAMLError as e:
        print(f"⚠ Error parsing YAML in {md_file.name}: {e}")
        chunks_skipped += 1
        continue

print(f"\n✓ Tract metadata added to {chunks_updated} chunks")
print(f"  Skipped: {chunks_skipped} (already had tract or errors)")
print(f"  Total: {chunks_updated + chunks_skipped}/71 processed")

# Distribution summary
if chunks_updated > 0:
    print("\nRe-run generate_manifest_71.py to update manifest with tract field.")
