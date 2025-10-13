#!/usr/bin/env python3
"""Analyze constraint density across all chunks.

Phase 8: Step 1 - Baseline constraint analysis before enhancement.
"""

import json
from pathlib import Path
from collections import Counter
from typing import Dict, List, Any


def analyze_chunk(chunk_path: Path) -> Dict[str, Any]:
    """Analyze constraint density for a single chunk."""
    try:
        data = json.loads(chunk_path.read_text())
        constraints = data.get('constraints', [])

        # Categorize constraint types
        has_tract_balance = any('tract' in c.get('name', '').lower() or 'balance' in c.get('name', '').lower()
                                for c in constraints)
        has_dimension_floor = any('floor' in c.get('name', '').lower() or 'min' in c.get('name', '').lower()
                                  for c in constraints)
        has_unit_sum = any('sum' in c.get('name', '').lower() or 'total' in c.get('name', '').lower()
                           for c in constraints)

        # Check for trivial constraints (true/placeholder)
        non_trivial_constraints = [c for c in constraints
                                   if c.get('expr', '').lower() not in ['true', 'false', '']]

        return {
            'chunk_id': data['id'],
            'title': data.get('title', 'Unknown'),
            'total_constraints': len(constraints),
            'non_trivial_constraints': len(non_trivial_constraints),
            'constraint_names': [c.get('name', 'unnamed') for c in constraints],
            'has_tract_balance': has_tract_balance,
            'has_dimension_floor': has_dimension_floor,
            'has_unit_sum': has_unit_sum,
            'is_trivial': len(non_trivial_constraints) <= 1,
            'is_placeholder_only': all(c.get('expr', '').lower() == 'true' for c in constraints)
        }
    except Exception as e:
        return {
            'chunk_id': chunk_path.stem.split('-')[1].split('.')[0],
            'error': str(e)
        }


def main():
    chunks_dir = Path("true-dual-tract/chunks")

    if not chunks_dir.exists():
        print(f"ERROR: {chunks_dir} not found")
        return 1

    results = []

    # Analyze all chunks
    for chunk_file in sorted(chunks_dir.glob("chunk-*.constraints.json")):
        results.append(analyze_chunk(chunk_file))

    # Filter out errors
    valid_results = [r for r in results if 'error' not in r]
    error_results = [r for r in results if 'error' in r]

    # Statistics
    total_chunks = len(valid_results)
    trivial_count = sum(1 for r in valid_results if r['is_trivial'])
    placeholder_only_count = sum(1 for r in valid_results if r['is_placeholder_only'])
    has_tract_balance = sum(1 for r in valid_results if r['has_tract_balance'])
    has_dimension_floor = sum(1 for r in valid_results if r['has_dimension_floor'])
    has_3plus_constraints = sum(1 for r in valid_results if r['non_trivial_constraints'] >= 3)

    print("=" * 80)
    print("PHASE 8: CONSTRAINT DENSITY ANALYSIS")
    print("=" * 80)
    print()

    print(f"Total chunks analyzed: {total_chunks}")
    print(f"Analysis errors: {len(error_results)}")
    print()

    print("CONSTRAINT DENSITY:")
    print(f"  Trivial chunks (≤1 non-trivial constraint): {trivial_count} ({trivial_count/total_chunks*100:.1f}%)")
    print(f"  Placeholder-only chunks: {placeholder_only_count} ({placeholder_only_count/total_chunks*100:.1f}%)")
    print(f"  Chunks with ≥3 non-trivial constraints: {has_3plus_constraints} ({has_3plus_constraints/total_chunks*100:.1f}%)")
    print()

    print("CONSTRAINT TYPES:")
    print(f"  Chunks with tract balance: {has_tract_balance} ({has_tract_balance/total_chunks*100:.1f}%)")
    print(f"  Chunks with dimension floor: {has_dimension_floor} ({has_dimension_floor/total_chunks*100:.1f}%)")
    print()

    # Distribution of constraint counts
    constraint_counts = Counter(r['non_trivial_constraints'] for r in valid_results)
    print("CONSTRAINT COUNT DISTRIBUTION:")
    for count in sorted(constraint_counts.keys()):
        num_chunks = constraint_counts[count]
        print(f"  {count} constraints: {num_chunks} chunks ({num_chunks/total_chunks*100:.1f}%)")
    print()

    # List chunks needing enhancement (trivial or placeholder-only)
    needs_enhancement = [r for r in valid_results if r['is_trivial'] or r['is_placeholder_only']]
    print(f"CHUNKS NEEDING ENHANCEMENT: {len(needs_enhancement)}")
    print()

    if needs_enhancement:
        print("Chunk ID | Title | Non-Trivial Constraints | Status")
        print("-" * 80)
        for r in needs_enhancement[:20]:  # Show first 20
            status = "PLACEHOLDER" if r['is_placeholder_only'] else "TRIVIAL"
            print(f"{r['chunk_id']:>8} | {r['title'][:40]:<40} | {r['non_trivial_constraints']:>23} | {status}")

        if len(needs_enhancement) > 20:
            print(f"... and {len(needs_enhancement) - 20} more chunks")
    print()

    # List pilot chunks (06, 09, 19) for reference
    pilot_chunks = [r for r in valid_results if r['chunk_id'] in ['06', '09', '19']]
    if pilot_chunks:
        print("PILOT CHUNKS (reference baseline):")
        print("-" * 80)
        for r in pilot_chunks:
            print(f"Chunk {r['chunk_id']}: {r['non_trivial_constraints']} non-trivial constraints")
            print(f"  Names: {', '.join(r['constraint_names'])}")
        print()

    # Errors
    if error_results:
        print("ERRORS:")
        for r in error_results:
            print(f"  Chunk {r['chunk_id']}: {r['error']}")
        print()

    print("=" * 80)
    print("RECOMMENDATION:")
    if len(needs_enhancement) > total_chunks * 0.5:
        print(f"  {len(needs_enhancement)}/{total_chunks} chunks need enhancement (>{50}%)")
        print("  ACTION: Run enhance_constraints.py --all to de-trivialize")
    else:
        print(f"  {len(needs_enhancement)}/{total_chunks} chunks need enhancement (<{50}%)")
        print("  ACTION: Targeted enhancement recommended")
    print("=" * 80)

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
