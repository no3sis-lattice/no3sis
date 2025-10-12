#!/usr/bin/env python3
"""
Emergency repair: Replace inline X8 definitions with Duality.Base imports
Phase 5-Pre: Structural integrity restoration

Fixes:
1. Remove duplicate X8/N/unitary definitions from chunks
2. Add `import Duality.Base` and `open Duality`
3. Maintain all other content unchanged
"""

import re
import sys
from pathlib import Path
from typing import List


def fix_chunk_file(path: Path) -> bool:
    """Fix a single chunk file to use Duality.Base imports."""
    try:
        content = path.read_text(encoding="utf-8")
        original = content

        # Extract namespace name
        ns_match = re.search(r'^namespace (Chunk\d+)$', content, re.MULTILINE)
        if not ns_match:
            print(f"⚠ Skipping {path.name}: No namespace found", file=sys.stderr)
            return False

        namespace_name = ns_match.group(1)

        # Step 1: Update imports (after Mathlib import, before namespace)
        import_section = "import Mathlib.Data.Nat.Basic"
        new_import_section = "import Mathlib.Data.Nat.Basic\nimport Duality.Base"

        if "import Duality.Base" not in content:
            content = content.replace(import_section, new_import_section)

        # Step 2: Add `open Duality` after namespace declaration
        namespace_line = f"namespace {namespace_name}"
        namespace_with_open = f"namespace {namespace_name}\n\nopen Duality"

        if "open Duality" not in content:
            content = content.replace(namespace_line, namespace_with_open)

        # Step 3: Remove duplicate definitions (N, X8 structure, unitary)
        # Pattern 1: def N : ℕ := 100
        content = re.sub(
            r'^def N : ℕ := 100\n+',
            '',
            content,
            flags=re.MULTILINE
        )

        # Pattern 2: structure X8 ... deriving Repr (multi-line or one-line)
        # One-line invalid syntax: "structure X8 where\n  x1 x2 x3 x4 x5 x6 x7 x8 : Nat\nderiving Repr"
        content = re.sub(
            r'^structure X8 where\n  x1 x2 x3 x4 x5 x6 x7 x8 : Nat\nderiving Repr\n+',
            '',
            content,
            flags=re.MULTILINE
        )

        # Multi-line valid syntax (if any exists)
        content = re.sub(
            r'^structure X8 where\n(?:  x\d+ : Nat\n)+deriving Repr\n+',
            '',
            content,
            flags=re.MULTILINE
        )

        # Pattern 3: def unitary (x : X8) : Prop := ...
        content = re.sub(
            r'^def unitary \(x : X8\) : Prop :=\n  x\.x1 \+ x\.x2 \+ x\.x3 \+ x\.x4 \+ x\.x5 \+ x\.x6 \+ x\.x7 \+ x\.x8 = N\n+',
            '',
            content,
            flags=re.MULTILINE
        )

        # Step 4: Clean up excessive blank lines (no more than 2 consecutive)
        content = re.sub(r'\n{3,}', '\n\n', content)

        # Write if changed
        if content != original:
            path.write_text(content, encoding="utf-8")
            return True
        else:
            return False

    except Exception as e:
        print(f"✗ Error fixing {path.name}: {e}", file=sys.stderr)
        return False


def main() -> int:
    # Find all chunk Lean files
    base_dir = Path(__file__).resolve().parents[1]
    chunks_dir = base_dir / "formal" / "Duality" / "Chunks"

    if not chunks_dir.exists():
        print(f"Error: Chunks directory not found: {chunks_dir}", file=sys.stderr)
        return 1

    chunk_files = sorted(chunks_dir.glob("Chunk*.lean"))

    if not chunk_files:
        print("No chunk files found", file=sys.stderr)
        return 1

    print(f"Found {len(chunk_files)} chunk files to process...")

    fixed_count = 0
    skipped_count = 0

    for chunk_file in chunk_files:
        if fix_chunk_file(chunk_file):
            print(f"✓ Fixed: {chunk_file.name}")
            fixed_count += 1
        else:
            skipped_count += 1

    print(f"\nResults: {fixed_count} fixed, {skipped_count} skipped")

    return 0


if __name__ == "__main__":
    sys.exit(main())
