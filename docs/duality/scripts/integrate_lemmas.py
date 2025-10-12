#!/usr/bin/env python3
"""
Phase 5.6: Lemma Integration Script

Refactors Lean chunks to:
1. Import Duality.Base and Duality.Lemmas
2. Remove duplicate X8/N/unitary definitions
3. Replace inline constraints with lemma calls
4. Measure LOC reduction

Usage:
  python3 integrate_lemmas.py --chunk 06
  python3 integrate_lemmas.py --all
  python3 integrate_lemmas.py --pilot  # Refactor 3 pilot chunks
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Optional, List, Tuple

# Tier 1 conceptual chunks to skip (abstract set theory, not numeric X8)
SKIP_CHUNKS = ['01', '02', '03', '04', '05', '21', '23']


def measure_loc(content: str) -> int:
    """Count lines of code (excluding blank lines and comments)."""
    lines = content.split('\n')
    loc = 0
    for line in lines:
        stripped = line.strip()
        if stripped and not stripped.startswith('--') and not stripped.startswith('/-'):
            loc += 1
    return loc


def refactor_chunk_header(content: str, chunk_id: str) -> Tuple[str, int]:
    """
    Replace chunk header with imports.

    Before:
      /-
      Chunk XX: Title
      -/
      import Mathlib...
      namespace ChunkXX
      def N : ℕ := 100
      structure X8 where...
      def unitary...

    After:
      /-
      Chunk XX: Title
      -/
      import Duality.Base
      import Duality.Lemmas

      namespace ChunkXX
      open Duality
    """
    lines = content.split('\n')

    # Find the comment block end
    comment_end = 0
    for i, line in enumerate(lines):
        if line.strip() == '-/':
            comment_end = i
            break

    # Find namespace declaration
    namespace_idx = 0
    for i, line in enumerate(lines):
        if line.startswith(f'namespace Chunk{chunk_id}'):
            namespace_idx = i
            break

    # Find where domainConstraints starts
    domain_idx = len(lines)
    for i, line in enumerate(lines):
        if 'def domainConstraints' in line:
            domain_idx = i
            break

    # Build new header
    new_lines = []
    new_lines.extend(lines[:comment_end + 1])  # Keep comment block
    new_lines.append('')
    new_lines.append('import Duality.Base')
    new_lines.append('import Duality.Lemmas')
    new_lines.append('')
    new_lines.append(f'namespace Chunk{chunk_id}')
    new_lines.append('open Duality')
    new_lines.append('')

    # Add everything from domainConstraints onward
    new_lines.extend(lines[domain_idx:])

    new_content = '\n'.join(new_lines)

    # Calculate LOC saved
    old_header_loc = measure_loc('\n'.join(lines[comment_end + 1:domain_idx]))
    new_header_loc = measure_loc('\n'.join(new_lines[comment_end + 1:comment_end + 8]))
    loc_saved = old_header_loc - new_header_loc

    return new_content, loc_saved


def refactor_constraints(content: str, chunk_id: str) -> Tuple[str, int, List[str]]:
    """
    Replace inline constraints with lemma calls.

    Returns: (new_content, loc_saved, replacements_made)
    """
    result = content
    replacements = []
    original_loc = measure_loc(content)

    # Pattern 1: dimension_floor_dimN → dimensionFloor x.xN k
    pattern1 = re.compile(r'\(x\.x(\d+) >= (\d+)\)')
    def replace_dim_floor(match):
        dim, val = match.groups()
        replacements.append(f'dimensionFloor x.x{dim} {val}')
        return f'(dimensionFloor x.x{dim} {val})'
    result = pattern1.sub(replace_dim_floor, result)

    # Pattern 2: tract_minimum (sum expansion) → tractMinimum x start end k
    # Match: ((x.x1 + x.x2 + x.x3 + x.x4) >= 10)
    pattern2 = re.compile(r'\(\((x\.x1 \+ x\.x2 \+ x\.x3 \+ x\.x4)\) >= (\d+)\)')
    def replace_tract_min_1_4(match):
        val = match.group(2)
        replacements.append(f'tractMinimum x 1 4 {val}')
        return f'(tractMinimum x 1 4 {val})'
    result = pattern2.sub(replace_tract_min_1_4, result)

    # Pattern 2b: External tract (x5-x8)
    pattern2b = re.compile(r'\(\((x\.x5 \+ x\.x6 \+ x\.x7 \+ x\.x8)\) >= (\d+)\)')
    def replace_tract_min_5_8(match):
        val = match.group(2)
        replacements.append(f'tractMinimum x 5 8 {val}')
        return f'(tractMinimum x 5 8 {val})'
    result = pattern2b.sub(replace_tract_min_5_8, result)

    # Pattern 3: uniformity (all dims >= k) → uniformityConstraint x start end k
    # Match: ((x.x1 >= 1 ∧ x.x2 >= 1 ∧ x.x3 >= 1 ∧ x.x4 >= 1 ∧ x.x5 >= 1 ∧ x.x6 >= 1 ∧ x.x7 >= 1 ∧ x.x8 >= 1))
    pattern3 = re.compile(
        r'\(\(x\.x1 >= (\d+) ∧ x\.x2 >= \1 ∧ x\.x3 >= \1 ∧ x\.x4 >= \1 ∧ '
        r'x\.x5 >= \1 ∧ x\.x6 >= \1 ∧ x\.x7 >= \1 ∧ x\.x8 >= \1\)\)'
    )
    def replace_uniformity(match):
        val = match.group(1)
        replacements.append(f'uniformityConstraint x 1 8 {val}')
        return f'(uniformityConstraint x 1 8 {val})'
    result = pattern3.sub(replace_uniformity, result)

    # Pattern 4: bridgeBalance for abs patterns
    # Match: ((x.x1 : Int) - x.x2 ≤ 5 ∧ (x.x2 : Int) - x.x1 ≤ 5)
    pattern4 = re.compile(r'\(\(x\.x(\d+) : Int\) - x\.x(\d+) ≤ (\d+) ∧ \(x\.x\2 : Int\) - x\.x\1 ≤ \3\)')
    def replace_bridge_balance(match):
        i, j, val = match.groups()
        replacements.append(f'bridgeBalance x.x{i} x.x{j} {val}')
        return f'(bridgeBalance x.x{i} x.x{j} {val})'
    result = pattern4.sub(replace_bridge_balance, result)

    # Pattern 5: primeAlignment (mod patterns - both % and mod keyword)
    # Match: (x.x1 % 2 = 0) or (x.x1 mod 2 = 0)
    pattern5a = re.compile(r'\(x\.x(\d+) % (\d+) = 0\)')
    pattern5b = re.compile(r'x\.x(\d+) mod (\d+) = 0')
    def replace_prime_align(match):
        dim, prime = match.groups()
        replacements.append(f'primeAlignment x.x{dim} {prime}')
        return f'primeAlignment x.x{dim} {prime}'
    result = pattern5a.sub(replace_prime_align, result)
    result = pattern5b.sub(replace_prime_align, result)

    new_loc = measure_loc(result)
    loc_saved = original_loc - new_loc

    return result, loc_saved, replacements


def refactor_chunk_file(file_path: Path, dry_run: bool = False) -> Tuple[bool, int, List[str]]:
    """
    Refactor a single chunk file.

    Returns: (success, loc_saved, replacements_made)
    """
    try:
        content = file_path.read_text(encoding='utf-8')
        original_loc = measure_loc(content)

        # Extract chunk ID
        match = re.search(r'Chunk(\d+)\.lean', file_path.name)
        if not match:
            return False, 0, []
        chunk_id = match.group(1)

        # Skip Tier 1 conceptual chunks
        if chunk_id in SKIP_CHUNKS:
            print(f"⏭️  Skipping {file_path.name} (Tier 1 conceptual chunk)")
            return True, 0, []

        # Step 1: Refactor header (imports + remove duplicates)
        content, header_loc_saved = refactor_chunk_header(content, chunk_id)

        # Step 2: Refactor constraints (inline → lemmas)
        content, constraints_loc_saved, replacements = refactor_constraints(content, chunk_id)

        total_loc_saved = header_loc_saved + constraints_loc_saved
        new_loc = measure_loc(content)

        if not dry_run:
            file_path.write_text(content, encoding='utf-8')
            print(f"✅ {file_path.name}: {original_loc} → {new_loc} LOC ({-total_loc_saved:+d}), {len(replacements)} lemmas")
        else:
            print(f"[DRY RUN] {file_path.name}: {original_loc} → {new_loc} LOC ({-total_loc_saved:+d}), {len(replacements)} lemmas")

        return True, total_loc_saved, replacements

    except Exception as e:
        print(f"❌ Error processing {file_path.name}: {e}", file=sys.stderr)
        return False, 0, []


def main():
    parser = argparse.ArgumentParser(description="Phase 5.6: Integrate lemmas into chunks")
    parser.add_argument('--chunk', type=str, help='Chunk ID to refactor (e.g., 06)')
    parser.add_argument('--all', action='store_true', help='Refactor all chunks (excluding Tier 1)')
    parser.add_argument('--pilot', action='store_true', help='Refactor 3 pilot chunks (06, 09, 19)')
    parser.add_argument('--dry-run', action='store_true', help='Show changes without writing')
    parser.add_argument('--base-dir', type=Path, default=Path(__file__).resolve().parents[1],
                       help='Base duality directory')

    args = parser.parse_args()

    if not (args.chunk or args.all or args.pilot):
        parser.error("Must specify --chunk, --all, or --pilot")

    chunks_dir = args.base_dir / 'formal' / 'Duality' / 'Chunks'

    # Determine which chunks to process
    if args.pilot:
        chunk_ids = ['06', '09', '19']
    elif args.all:
        # All chunks except Tier 1
        chunk_ids = [f'{i:02d}' for i in range(1, 63) if f'{i:02d}' not in SKIP_CHUNKS]
    else:
        chunk_ids = [f'{int(args.chunk):02d}']

    print(f"{'='*70}")
    print(f"Phase 5.6: Lemma Integration")
    print(f"{'='*70}")
    print(f"Processing {len(chunk_ids)} chunks...")
    if args.dry_run:
        print("⚠️  DRY RUN MODE - No files will be modified")
    print()

    total_loc_saved = 0
    success_count = 0
    all_replacements = []

    for chunk_id in chunk_ids:
        file_path = chunks_dir / f'Chunk{chunk_id}.lean'
        if not file_path.exists():
            print(f"⚠️  File not found: {file_path.name}")
            continue

        success, loc_saved, replacements = refactor_chunk_file(file_path, args.dry_run)
        if success:
            success_count += 1
            total_loc_saved += loc_saved
            all_replacements.extend(replacements)

    print()
    print(f"{'='*70}")
    print(f"Summary:")
    print(f"  Chunks processed: {success_count}/{len(chunk_ids)}")
    print(f"  Total LOC saved: {total_loc_saved} lines")
    print(f"  Total lemma replacements: {len(all_replacements)}")
    print(f"  Average LOC saved per chunk: {total_loc_saved / success_count if success_count > 0 else 0:.1f}")
    print(f"{'='*70}")

    if args.dry_run:
        print("\n⚠️  This was a dry run. Use without --dry-run to apply changes.")

    return 0 if success_count == len(chunk_ids) else 1


if __name__ == '__main__':
    sys.exit(main())
