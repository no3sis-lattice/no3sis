#!/usr/bin/env python3
"""Mark conceptual chunks as documentation type.

Phase 8: Categorize chunks by computational vs. documentation goals.
"""

import json
from pathlib import Path
from typing import List

# Chunks identified as documentation (from Phase 8 analysis)
# These describe system architecture, not manifold constraints
DOCUMENTATION_CHUNKS = ["01", "02", "03", "04", "05"]

# Chunks with struct/type issues needing manual formalization
DEFERRED_CHUNKS = ["19", "21"]


def mark_chunk(chunk_id: str, goal_type: str, base_dir: Path) -> bool:
    """Mark chunk with specific goal type.

    Args:
        chunk_id: Two-digit chunk ID (e.g., "01")
        goal_type: One of "computational", "documentation", "deferred"
        base_dir: Base directory containing chunks/

    Returns:
        True if successfully marked, False if file not found
    """
    chunk_file = base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id}.constraints.json"

    if not chunk_file.exists():
        print(f"⚠ Warning: {chunk_file} not found")
        return False

    # Read, update, write
    data = json.loads(chunk_file.read_text())
    data['goalType'] = goal_type

    chunk_file.write_text(json.dumps(data, indent=2) + '\n')
    print(f"✓ Chunk {chunk_id}: goalType = {goal_type}")
    return True


def main():
    """Mark all documentation and deferred chunks."""
    base_dir = Path(__file__).parent.parent

    print("=" * 60)
    print("Phase 8: Marking Documentation Chunks")
    print("=" * 60)

    # Mark documentation chunks
    print("\n📚 Documentation Chunks (conceptual architecture):")
    doc_success = sum(
        mark_chunk(chunk_id, "documentation", base_dir)
        for chunk_id in DOCUMENTATION_CHUNKS
    )

    # Mark deferred chunks
    print("\n⏸ Deferred Chunks (complex type constraints):")
    def_success = sum(
        mark_chunk(chunk_id, "deferred", base_dir)
        for chunk_id in DEFERRED_CHUNKS
    )

    # Summary
    total_marked = doc_success + def_success
    computational = 62 - total_marked

    print("\n" + "=" * 60)
    print("Summary:")
    print("=" * 60)
    print(f"Documentation:  {doc_success}/{len(DOCUMENTATION_CHUNKS)}")
    print(f"Deferred:       {def_success}/{len(DEFERRED_CHUNKS)}")
    print(f"Total marked:   {total_marked}/62")
    print(f"Computational:  {computational}/62 (implicit, default)")
    print("=" * 60)

    if total_marked != len(DOCUMENTATION_CHUNKS) + len(DEFERRED_CHUNKS):
        print("\n⚠ Warning: Some chunks were not found!")
        return 1

    return 0


if __name__ == "__main__":
    exit(main())
