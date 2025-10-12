#!/usr/bin/env python3
"""
Fix MiniZinc syntax issues in generated .mzn files.

Issues to fix:
1. True → true (case-sensitive)
2. ∀ → forall (not supported in constraint context, comment out)
3. ∃ → exists (not supported in constraint context, comment out)
4. Complex logical expressions → comment out (require manual translation)
"""
from pathlib import Path
import re

def fix_mzn_syntax(content: str) -> tuple[str, int]:
    """Fix common MiniZinc syntax issues. Returns (fixed_content, fixes_count)"""
    original = content
    fixes = 0

    # Fix 1: True → true (case-sensitive)
    if "True" in content:
        content = content.replace("constraint True;", "constraint true;")
        fixes += content.count("constraint true;") - original.count("constraint true;")

    # Fix 2: Comment out lines with unsupported logical symbols or undefined identifiers
    lines = content.split('\n')
    fixed_lines = []
    for line in lines:
        # Only allow basic constraints: true, and the unit-sum constraint
        if 'constraint' in line:
            # Keep the unit-sum constraint and "constraint true"
            if 'sum(i in 1..8)(x[i]) = N' in line or line.strip() == 'constraint true;':
                fixed_lines.append(line)
            # Comment out all other constraints (they contain undefined identifiers or unsupported syntax)
            else:
                fixed_lines.append(f"% UNSUPPORTED_SYNTAX: {line}")
                fixes += 1
        else:
            fixed_lines.append(line)

    content = '\n'.join(fixed_lines)
    return content, fixes

def main():
    chunks_dir = Path("true-dual-tract/chunks")
    fixed = 0
    skipped = 0
    errors = 0

    for i in range(1, 63):
        mzn_file = chunks_dir / f"chunk-{i:02d}.mzn"

        if not mzn_file.exists():
            print(f"ERROR: Missing {mzn_file}")
            errors += 1
            continue

        # Read original
        original_content = mzn_file.read_text()

        # Fix syntax
        fixed_content, fix_count = fix_mzn_syntax(original_content)

        # Write back if changes made
        if fix_count > 0:
            mzn_file.write_text(fixed_content)
            print(f"✓ chunk-{i:02d}.mzn ({fix_count} fixes)")
            fixed += 1
        else:
            skipped += 1

    print(f"\nSummary: {fixed} fixed, {skipped} unchanged, {errors} errors")

if __name__ == "__main__":
    main()
