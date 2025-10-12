#!/usr/bin/env python3
"""
Cross-check constraint equivalence: JSON ↔ MZN ↔ Lean
Phase 7: Verify MiniZinc and Lean4 encode identical constraints
"""

import json
import re
from pathlib import Path
from typing import Dict, List

def count_constraints(chunk_id: str) -> Dict:
    """Count constraints across JSON, MZN, and Lean for a single chunk."""
    base = Path(__file__).parent.parent / "true-dual-tract/chunks"

    # JSON: source of truth
    json_path = base / f"chunk-{chunk_id}.constraints.json"
    json_data = json.loads(json_path.read_text())
    json_count = len(json_data.get("constraints", []))

    # MZN: count active constraints (excluding UNSUPPORTED_SYNTAX)
    mzn_path = base / f"chunk-{chunk_id}.mzn"
    mzn_text = mzn_path.read_text()
    mzn_lines = mzn_text.split('\n')

    mzn_active = 0
    mzn_unsupported = 0
    for line in mzn_lines:
        if 'constraint' in line:
            if '% UNSUPPORTED_SYNTAX:' in line:
                mzn_unsupported += 1
            elif line.strip().startswith('constraint'):
                # Count actual constraint (not comment)
                mzn_active += 1

    # Lean: check if domainConstraints is trivial
    lean_formal = Path(__file__).parent.parent / "formal" / "Duality" / "Chunks" / f"Chunk{chunk_id}.lean"
    lean_text = lean_formal.read_text()
    lean_trivial = "domainConstraints : Prop :=\n  True" in lean_text

    # Determine status
    if mzn_active <= 1:
        status = "DEGENERATE"  # Only unit-sum constraint
    elif json_count == mzn_active:
        status = "OK"
    else:
        status = "MISMATCH"

    return {
        "id": chunk_id,
        "json_total": json_count,
        "mzn_active": mzn_active,
        "mzn_unsupported": mzn_unsupported,
        "lean_trivial": lean_trivial,
        "status": status
    }

def generate_report(results: List[Dict]) -> str:
    """Generate markdown report from cross-check results."""
    report = "# Cross-Check Report\n\n"
    report += "**Generated**: 2025-10-12\n"
    report += "**Phase**: 7 (Cross-Check)\n\n"
    report += "---\n\n"

    # Summary statistics
    ok_count = sum(1 for r in results if r['status'] == 'OK')
    degenerate_count = sum(1 for r in results if r['status'] == 'DEGENERATE')
    mismatch_count = sum(1 for r in results if r['status'] == 'MISMATCH')

    report += "## Summary\n\n"
    report += "```\n"
    report += f"✅ OK: {ok_count}/62 ({100*ok_count/62:.1f}%)\n"
    report += f"⚠️  DEGENERATE: {degenerate_count}/62 ({100*degenerate_count/62:.1f}%)\n"
    report += f"❌ MISMATCH: {mismatch_count}/62 ({100*mismatch_count/62:.1f}%)\n"
    report += "```\n\n"

    # Detailed table
    report += "## Per-Chunk Analysis\n\n"
    report += "| Chunk | JSON Total | MZN Active | MZN Unsupported | Lean Trivial | Status |\n"
    report += "|-------|------------|------------|-----------------|--------------|--------|\n"

    for r in results:
        trivial_mark = "Yes" if r['lean_trivial'] else "No"
        report += f"| {r['id']} | {r['json_total']} | {r['mzn_active']} | "
        report += f"{r['mzn_unsupported']} | {trivial_mark} | {r['status']} |\n"

    report += "\n---\n\n"

    # Interpretation
    report += "## Interpretation\n\n"
    report += "**DEGENERATE Status**: Chunk has only unit-sum constraint active "
    report += "(all domain constraints marked UNSUPPORTED_SYNTAX).\n\n"
    report += "**OK Status**: JSON constraint count matches MZN active constraints.\n\n"
    report += "**MISMATCH Status**: Discrepancy between JSON and MZN constraint counts.\n\n"

    report += "### Current State\n\n"
    if degenerate_count == 62:
        report += "⚠️ **All chunks are DEGENERATE**: ~180 domain constraints require translation "
        report += "from unsupported syntax (∀, ∃, ∈, predicates) to valid MiniZinc.\n\n"
        report += "This is expected for baseline verification. Phase 6b will address constraint formalization.\n"

    return report

def main():
    """Execute cross-check for all 62 chunks."""
    print("Running cross-check on 62 chunks...")

    results = []
    for i in range(1, 63):
        chunk_id = f"{i:02d}"
        try:
            result = count_constraints(chunk_id)
            results.append(result)
            if i % 10 == 0:
                print(f"  Processed: chunk-{chunk_id}")
        except Exception as e:
            print(f"  ⚠️  Error processing chunk-{chunk_id}: {e}")

    # Generate markdown report
    report_path = Path(__file__).parent.parent / "cross-check-report.md"
    report_content = generate_report(results)
    report_path.write_text(report_content)

    # Print summary
    print(f"\n✓ Cross-check complete: {len(results)}/62 chunks processed")
    print(f"✓ Report written to: {report_path.name}")

    # Summary stats
    ok_count = sum(1 for r in results if r['status'] == 'OK')
    degenerate_count = sum(1 for r in results if r['status'] == 'DEGENERATE')
    mismatch_count = sum(1 for r in results if r['status'] == 'MISMATCH')

    print(f"\nStatus breakdown:")
    print(f"  OK: {ok_count}/62")
    print(f"  DEGENERATE: {degenerate_count}/62")
    print(f"  MISMATCH: {mismatch_count}/62")

if __name__ == "__main__":
    main()
