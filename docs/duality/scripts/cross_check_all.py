#!/usr/bin/env python3
"""
Cross-check constraint equivalence: JSON ↔ MZN ↔ Lean
Phase 7: Verify MiniZinc and Lean4 encode identical constraints

Enhancements:
- Constraint-name extraction and SHA-256 checksum comparison across JSON/MZN/Lean
- Fallback to count-based comparison when names are unavailable
- Dynamic chunk discovery (no hard-coded 62)
- Robust Lean trivial detection
- CLI flags: --base-dir, --format, --warn-only, --chunks, --report
- JSON output option and per-chunk diff samples
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple
import hashlib


# --------------------------
# Utilities
# --------------------------

def sha256_hex(lines: Iterable[str]) -> str:
    h = hashlib.sha256()
    for line in lines:
        h.update(line.encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()

def uniq_sorted(names: Iterable[str]) -> List[str]:
    return sorted({n.strip() for n in names if isinstance(n, str) and n.strip()})

def now_iso() -> str:
    return dt.datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S UTC")


# --------------------------
# Extraction helpers
# --------------------------

JSON_NAME_KEYS = ("name", "id", "label", "constraint")

def extract_names_from_json_constraints(obj) -> List[str]:
    # Expecting { "constraints": [ { "name": "...", ... }, ... ] }
    names: List[str] = []
    if not isinstance(obj, dict):
        return names
    constraints = obj.get("constraints", [])
    if isinstance(constraints, list):
        for c in constraints:
            if isinstance(c, dict):
                for k in JSON_NAME_KEYS:
                    v = c.get(k)
                    if isinstance(v, str):
                        names.append(v)
                        break
    return uniq_sorted(names)

# MZN patterns:
RX_MZN_ACTIVE = re.compile(r"^\s*constraint\b")
RX_MZN_UNSUPPORTED = re.compile(r"UNSUPPORTED_SYNTAX")
# Name annotations: either preceding or trailing comments
RX_MZN_COMMENT_NAME = re.compile(r"^\s*%+\s*(?:constraint|c|name)\s*:\s*(?P<name>.+?)\s*$", re.IGNORECASE)
RX_MZN_TRAIL_NAME = re.compile(r"%+\s*(?:constraint|c|name)\s*:\s*(?P<name>.+?)\s*$", re.IGNORECASE)

def extract_from_mzn(path: Path) -> Tuple[int, int, List[str]]:
    names: List[str] = []
    mzn_text = path.read_text(encoding="utf-8", errors="ignore")
    lines = mzn_text.splitlines()
    mzn_active = 0
    mzn_unsupported = 0
    pending_name: Optional[str] = None

    for line in lines:
        if RX_MZN_UNSUPPORTED.search(line):
            mzn_unsupported += 1

        m = RX_MZN_COMMENT_NAME.search(line)
        if m:
            pending_name = m.group("name").strip()
            continue

        if RX_MZN_ACTIVE.match(line.strip()):
            mzn_active += 1
            # trailing comment name
            mt = RX_MZN_TRAIL_NAME.search(line)
            if mt:
                names.append(mt.group("name").strip())
            elif pending_name:
                names.append(pending_name)
            pending_name = None
        else:
            # no-op for non-constraint line
            pass

    return mzn_active, mzn_unsupported, uniq_sorted(names)

# Lean patterns:
RX_LEAN_TRIVIAL = re.compile(r"domainConstraints\s*:\s*Prop\s*:=\s*True")
RX_LEAN_LINE_NAME = re.compile(r"^\s*--+\s*constraint\s*:\s*(?P<name>.+?)\s*$", re.IGNORECASE)
RX_LEAN_BLOCK_NAME = re.compile(r"/--\s*constraint\s*:\s*(?P<name>.+?)\s*-\s*/", re.IGNORECASE | re.S)
RX_LEAN_ATTR = re.compile(r"^\s*@\[constraint\]\s*(?:theorem|def|lemma|example)?\s+(?P<name>[A-Za-z0-9_']+)", re.IGNORECASE)

def extract_from_lean(path: Path) -> Tuple[bool, List[str]]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    lean_trivial = bool(RX_LEAN_TRIVIAL.search(text))
    names: Set[str] = set()
    for line in text.splitlines():
        m = RX_LEAN_LINE_NAME.search(line)
        if m:
            names.add(m.group("name").strip())
        a = RX_LEAN_ATTR.search(line)
        if a:
            names.add(a.group("name").strip())
    for b in RX_LEAN_BLOCK_NAME.finditer(text):
        names.add(b.group("name").strip())
    return lean_trivial, uniq_sorted(names)


# --------------------------
# Data classes
# --------------------------

@dataclass
class ChunkResult:
    id: str
    json_total: int
    mzn_active: int
    mzn_unsupported: int
    lean_trivial: bool
    status: str
    json_names: List[str]
    mzn_names: List[str]
    lean_names: List[str]
    checksum_json: str
    checksum_mzn: str
    checksum_lean: str
    files: Dict[str, str]
    error: str = ""
    warnings: List[str] = None

    def __post_init__(self):
        if self.warnings is None:
            self.warnings = []

@dataclass
class Summary:
    total: int
    ok: int
    degenerate: int
    mismatch: int
    insufficient: int
    error: int


# --------------------------
# Core logic
# --------------------------

def discover_chunks(base_chunks_dir: Path) -> List[str]:
    # discover by chunk-XX.constraints.json
    ids: List[str] = []
    for p in sorted(base_chunks_dir.glob("chunk-*.constraints.json")):
        m = re.search(r"chunk-(\d+)\.constraints\.json$", p.name)
        if m:
            ids.append(f"{int(m.group(1)):02d}")
    return ids

def count_and_names_for_chunk(chunk_id: str, base_dir: Path) -> ChunkResult:
    base_chunks = base_dir / "true-dual-tract" / "chunks"
    json_path = base_chunks / f"chunk-{chunk_id}.constraints.json"
    mzn_path = base_chunks / f"chunk-{chunk_id}.mzn"
    lean_path = base_dir / "formal" / "Duality" / "Chunks" / f"Chunk{chunk_id}.lean"

    files = {
        "json": str(json_path),
        "mzn": str(mzn_path),
        "lean": str(lean_path),
    }

    try:
        # JSON
        json_data = json.loads(json_path.read_text(encoding="utf-8"))
        json_total = len(json_data.get("constraints", []))
        json_names = extract_names_from_json_constraints(json_data)

        # MZN
        mzn_active, mzn_unsupported, mzn_names = extract_from_mzn(mzn_path)

        # Lean
        lean_trivial, lean_names = extract_from_lean(lean_path)

        # Checksums
        checksum_json = sha256_hex(json_names)
        checksum_mzn = sha256_hex(mzn_names)
        checksum_lean = sha256_hex(lean_names)

        # Warnings collection
        warnings = []

        # ENHANCEMENT 1.1a: Warn if MZN annotation coverage is incomplete
        if mzn_active > 1 and len(mzn_names) < mzn_active:
            coverage_pct = 100.0 * len(mzn_names) / mzn_active if mzn_active > 0 else 0
            warnings.append(f"MZN annotation coverage: {len(mzn_names)}/{mzn_active} ({coverage_pct:.0f}%)")

        # Determine status
        # Prefer name-based comparison if at least two modalities have non-empty name sets
        modalities = []
        if json_names:
            modalities.append(("json", checksum_json, set(json_names)))
        if mzn_names:
            modalities.append(("mzn", checksum_mzn, set(mzn_names)))
        if lean_names:
            modalities.append(("lean", checksum_lean, set(lean_names)))

        # ENHANCEMENT 1.1b: Detect INSUFFICIENT status (empty name sets force proper annotations)
        empty_count = sum(1 for m in [("json", json_names), ("mzn", mzn_names), ("lean", lean_names)] if not m[1])

        if len(modalities) >= 2:
            checks = {c for _, c, _ in modalities}
            status = "OK" if len(checks) == 1 else "MISMATCH"
        elif empty_count >= 2 and mzn_active > 1:
            # Force annotation if 2+ modalities have no names and non-trivial constraints exist
            status = "INSUFFICIENT"
            warnings.append(f"Insufficient name annotations: {3 - empty_count}/3 modalities have names")
        else:
            # Fallback to count-based analysis
            if mzn_active <= 1:
                status = "DEGENERATE"
            elif json_total == mzn_active:
                status = "OK"
            else:
                status = "MISMATCH"

        return ChunkResult(
            id=chunk_id,
            json_total=json_total,
            mzn_active=mzn_active,
            mzn_unsupported=mzn_unsupported,
            lean_trivial=lean_trivial,
            status=status,
            json_names=json_names,
            mzn_names=mzn_names,
            lean_names=lean_names,
            checksum_json=checksum_json,
            checksum_mzn=checksum_mzn,
            checksum_lean=checksum_lean,
            files=files,
            warnings=warnings,
        )

    except Exception as e:
        return ChunkResult(
            id=chunk_id,
            json_total=0,
            mzn_active=0,
            mzn_unsupported=0,
            lean_trivial=False,
            status="ERROR",
            json_names=[],
            mzn_names=[],
            lean_names=[],
            checksum_json="",
            checksum_mzn="",
            checksum_lean="",
            files=files,
            error=str(e),
            warnings=[],
        )


def summarize(results: List[ChunkResult]) -> Summary:
    return Summary(
        total=len(results),
        ok=sum(1 for r in results if r.status == "OK"),
        degenerate=sum(1 for r in results if r.status == "DEGENERATE"),
        mismatch=sum(1 for r in results if r.status == "MISMATCH"),
        insufficient=sum(1 for r in results if r.status == "INSUFFICIENT"),
        error=sum(1 for r in results if r.status == "ERROR"),
    )


# --------------------------
# Rendering
# --------------------------

def render_text(results: List[ChunkResult], base_total: int) -> str:
    ok = sum(1 for r in results if r.status == "OK")
    deg = sum(1 for r in results if r.status == "DEGENERATE")
    mis = sum(1 for r in results if r.status == "MISMATCH")
    insuf = sum(1 for r in results if r.status == "INSUFFICIENT")
    err = sum(1 for r in results if r.status == "ERROR")

    def pct(n: int) -> float:
        return (100.0 * n / base_total) if base_total > 0 else 0.0

    lines: List[str] = []
    lines.append("# Cross-Check Report")
    lines.append("")
    lines.append(f"Generated: {now_iso()}")
    lines.append("Phase: 7 (Cross-Check)")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append("```")
    lines.append(f"OK: {ok}/{base_total} ({pct(ok):.1f}%)")
    lines.append(f"DEGENERATE: {deg}/{base_total} ({pct(deg):.1f}%)")
    lines.append(f"MISMATCH: {mis}/{base_total} ({pct(mis):.1f}%)")
    lines.append(f"INSUFFICIENT: {insuf}/{base_total} ({pct(insuf):.1f}%)")
    lines.append(f"ERROR: {err}/{base_total} ({pct(err):.1f}%)")
    lines.append("```")
    lines.append("")
    lines.append("## Per-Chunk Analysis")
    lines.append("")
    lines.append("| Chunk | JSON Total | MZN Active | MZN Unsupported | Lean Trivial | Status | Checksums (J/M/L) |")
    lines.append("|-------|------------|------------|-----------------|--------------|--------|-------------------|")

    for r in sorted(results, key=lambda x: x.id):
        lines.append(
            f"| {r.id} | {r.json_total} | {r.mzn_active} | {r.mzn_unsupported} | "
            f"{'Yes' if r.lean_trivial else 'No'} | {r.status} | "
            f"{r.checksum_json[:8]}/{r.checksum_mzn[:8]}/{r.checksum_lean[:8]} |"
        )

    # Diff samples for mismatches
    difflines: List[str] = []
    for r in sorted(results, key=lambda x: x.id):
        if r.status == "MISMATCH":
            sJ, sM, sL = set(r.json_names), set(r.mzn_names), set(r.lean_names)
            alln = sorted(sJ | sM | sL)
            difflines.append("")
            difflines.append(f"### Diff sample for chunk {r.id} (J/M/L presence)")
            difflines.append("")
            difflines.append("```")
            for name in alln[:20]:
                marks = "".join([
                    "J" if name in sJ else "-",
                    "M" if name in sM else "-",
                    "L" if name in sL else "-",
                ])
                difflines.append(f"[{marks}] {name}")
            difflines.append("```")

    if difflines:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append("## Mismatch Samples")
        lines.extend(difflines)

    # Warnings section (if any warnings exist)
    warnings_exist = any(r.warnings for r in results)
    if warnings_exist:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append("## Warnings")
        lines.append("")
        for r in sorted(results, key=lambda x: x.id):
            if r.warnings:
                lines.append(f"### Chunk {r.id}")
                lines.append("```")
                for w in r.warnings:
                    lines.append(f"⚠  {w}")
                lines.append("```")
                lines.append("")

    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Interpretation")
    lines.append("")
    lines.append("DEGENERATE: Only the unit/structural constraint is active in MiniZinc.")
    lines.append("OK: Name checksums match across modalities, or counts match if names are unavailable.")
    lines.append("MISMATCH: Name checksums differ (preferred) or counts differ (fallback).")
    lines.append("INSUFFICIENT: 2+ modalities have empty name sets (proper annotations required for parity check).")
    return "\n".join(lines)


def render_json(results: List[ChunkResult]) -> str:
    payload = {
        "generated": now_iso(),
        "phase": 7,
        "results": [
            {
                "id": r.id,
                "status": r.status,
                "json_total": r.json_total,
                "mzn_active": r.mzn_active,
                "mzn_unsupported": r.mzn_unsupported,
                "lean_trivial": r.lean_trivial,
                "checksums": {
                    "json": r.checksum_json,
                    "mzn": r.checksum_mzn,
                    "lean": r.checksum_lean,
                },
                "names": {
                    "json": r.json_names,
                    "mzn": r.mzn_names,
                    "lean": r.lean_names,
                },
                "files": r.files,
                "error": r.error,
                "warnings": r.warnings,
            }
            for r in results
        ],
    }
    return json.dumps(payload, indent=2)


# --------------------------
# CLI
# --------------------------

def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Cross-check constraint equivalence across JSON/MZN/Lean.")
    # Default base is docs/duality (this script lives at docs/duality/scripts)
    default_base = Path(__file__).resolve().parents[1]
    parser.add_argument("--base-dir", type=Path, default=default_base, help=f"Base duality directory (default: {default_base})")
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format")
    parser.add_argument("--warn-only", action="store_true", help="Exit 0 even when mismatches/errors occur")
    parser.add_argument("--chunks", nargs="*", help="Specific chunk ids to process (e.g., 04 06 09). Default: auto-discover all")
    parser.add_argument("--report", type=Path, default=None, help="Write Markdown report to path (text mode only)")
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)
    base_dir = args.base_dir
    base_chunks = base_dir / "true-dual-tract" / "chunks"

    if not base_chunks.exists():
        print(f"Error: chunks path not found: {base_chunks}", file=sys.stderr)
        return 2

    if args.chunks:
        chunk_ids = [f"{int(x):02d}" for x in args.chunks]
    else:
        chunk_ids = discover_chunks(base_chunks)

    if not chunk_ids:
        print("No chunks discovered.", file=sys.stderr)
        return 1

    results: List[ChunkResult] = []
    for idx, cid in enumerate(chunk_ids, 1):
        r = count_and_names_for_chunk(cid, base_dir)
        results.append(r)
        if idx % 10 == 0:
            print(f"Processed chunk-{cid} ({idx}/{len(chunk_ids)})")

    # Render
    if args.format == "json":
        out = render_json(results)
        print(out)
    else:
        out = render_text(results, len(chunk_ids))
        if args.report:
            args.report.write_text(out, encoding="utf-8")
            print(f"Wrote report to: {args.report}")
        else:
            print(out)

    # Exit code
    if args.warn_only:
        return 0

    # Fail if any mismatch, insufficient, or error
    has_fail = any(r.status in ("MISMATCH", "INSUFFICIENT", "ERROR") for r in results)
    return 1 if has_fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
