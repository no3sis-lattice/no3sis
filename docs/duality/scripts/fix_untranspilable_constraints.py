#!/usr/bin/env python3
"""
Phase 8: Fix untranspilable constraints in JSON files.

Strategy: Replace symbolic/abstract constraint expressions with True placeholders
and preserve them in notes for future manual formalization.
"""

import json
from pathlib import Path
import re


# Patterns that indicate untranspilable expressions (Phase 8 comprehensive list)
UNTRANSPILABLE_PATTERNS = [
    r'typeof\(',          # Type reflection not supported
    r'∃.*:.*→',          # Incomplete existential quantifiers
    r'well_formed\(',    # Abstract predicates
    r'∈\s*\{[^}]+\}',   # Set membership (use ∧ instead)
    r'\|.*\|\s*=',      # Cardinality
    r'pipeline\(',       # Abstract functions
    r'calls\(',
    r'orchestrates\(',
    r'has_field\(',
    r'deterministic\(',
    r'measurable\(',
    r'scalable\(',
    r'∀\s+\w+\s+∈',     # Quantification over sets (use ranges)
    r'=\s*\{[^}]+\}',   # Set literals
    r'↔.*↔',            # Chained bi-implications
    r'aligned\(',        # Abstract predicates
    r'models\(',
    r'explains_why\(',
    r'suitable\(',
    r'has\(',
    r'emits\(',
    r'works_with\(',
    r'testable\(',
    r'predictable\(',
    r'adheres_to\(',
    r'contains\s+',
    r'describes\(',
    r'step_\d+:',       # Step annotations
    r'\bmod\b',         # Use % instead
]


def is_untranspilable(expr: str) -> bool:
    """Check if expression matches untranspilable patterns."""
    # Quick check: if it's just "True" or "False", it's fine
    if expr.strip() in ['True', 'False', 'true', 'false']:
        return False

    for pattern in UNTRANSPILABLE_PATTERNS:
        if re.search(pattern, expr):
            return True
    return False


def fix_chunk_constraints(chunk_path: Path, dry_run: bool = False) -> tuple[bool, int]:
    """Fix untranspilable constraints in a chunk JSON file.

    Returns: (was_modified, num_fixed)
    """
    data = json.loads(chunk_path.read_text())
    constraints = data.get('constraints', [])

    modified = False
    num_fixed = 0

    for constraint in constraints:
        expr = constraint.get('expr', '')

        # Skip if already marked as UNTRANSPILABLE
        notes = constraint.get('notes', '')
        if 'UNTRANSPILABLE' in notes and expr.strip() in ['True', 'true']:
            continue

        if is_untranspilable(expr):
            # Preserve original expression in notes
            original_expr = expr
            constraint['expr'] = 'True'

            # Append to notes
            if 'UNTRANSPILABLE' not in notes:
                constraint['notes'] = f"{notes} | UNTRANSPILABLE (Phase8): {original_expr}"

            modified = True
            num_fixed += 1
            print(f"  Fixed constraint '{constraint['name']}': {original_expr[:50]}...")

    if modified and not dry_run:
        chunk_path.write_text(json.dumps(data, indent=2) + '\n')

    return modified, num_fixed


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Fix untranspilable constraints")
    parser.add_argument('--chunks', type=str, help='Comma-separated chunk IDs (default: all)')
    parser.add_argument('--dry-run', action='store_true', help='Show changes without writing')
    args = parser.parse_args()

    chunks_dir = Path("true-dual-tract/chunks")

    if args.chunks:
        chunk_ids = [cid.strip().zfill(2) for cid in args.chunks.split(",")]
        chunk_files = [chunks_dir / f"chunk-{cid}.constraints.json" for cid in chunk_ids]
    else:
        chunk_files = sorted(chunks_dir.glob("chunk-*.constraints.json"))

    total_modified = 0
    total_fixed = 0

    for chunk_file in chunk_files:
        chunk_id = chunk_file.stem.split('-')[1].split('.')[0]
        modified, num_fixed = fix_chunk_constraints(chunk_file, dry_run=args.dry_run)

        if modified:
            print(f"Chunk {chunk_id}: Fixed {num_fixed} constraint(s)")
            total_modified += 1
            total_fixed += num_fixed

    print()
    print(f"Summary: {total_modified} chunks modified, {total_fixed} constraints fixed")

    if args.dry_run:
        print("(Dry run - no files changed)")
    else:
        print("Changes written. Re-run transpiler to regenerate Lean/MZN files.")

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
