#!/usr/bin/env python3
"""
Assign Monster group prime factors to chunks deterministically.

- Adds/updates parameters.monsterPrimes in chunk-*.constraints.json
- Deterministic cyclic assignment across primes, supports multiple per chunk
- Safe defaults: k=2 primes per chunk, preserves existing and sorts

Usage:
  python assign_monster_primes.py --all --write
  python assign_monster_primes.py --chunks 06 09 19 --k 3 --write
  python assign_monster_primes.py --dry-run --chunks 06
"""
from __future__ import annotations
import argparse, json, re
from pathlib import Path

MONSTER_PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]

def discover_chunks(base_dir: Path) -> list[str]:
    chunks_dir = base_dir / "true-dual-tract" / "chunks"
    ids = []
    for p in sorted(chunks_dir.glob("chunk-*.constraints.json")):
        m = re.search(r"chunk-(\d+)\.constraints\.json$", p.name)
        if m:
            ids.append(f"{int(m.group(1)):02d}")
    return ids

def assign_for_chunk(cid: str, k: int) -> list[int]:
    base = int(cid)
    picks = []
    for j in range(k):
        picks.append(MONSTER_PRIMES[(base + j) % len(MONSTER_PRIMES)])
    return sorted(set(picks))

def update_chunk(base_dir: Path, cid: str, primes: list[int], write: bool) -> tuple[str, list[int], bool]:
    path = base_dir / "true-dual-tract" / "chunks" / f"chunk-{cid}.constraints.json"
    if not path.exists():
        return (cid, [], False)
    data = json.loads(path.read_text(encoding="utf-8"))
    params = data.setdefault("parameters", {})
    existing = params.get("monsterPrimes", [])
    merged = sorted(set(map(int, existing)) | set(primes))
    params["monsterPrimes"] = merged
    if write:
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return (cid, merged, True)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true", help="Process all discovered chunks")
    ap.add_argument("--chunks", nargs="+", help="Specific chunk IDs (e.g., 06 09 19)")
    ap.add_argument("--k", type=int, default=2, help="Number of primes to assign per chunk (default: 2)")
    ap.add_argument("--write", action="store_true", help="Write changes to files (otherwise dry run)")
    ap.add_argument("--dry-run", action="store_true", help="Alias for default (no write)")
    args = ap.parse_args()

    base = Path(__file__).resolve().parents[1]
    targets = []

    if args.all:
        targets = discover_chunks(base)
    elif args.chunks:
        targets = [f"{int(x):02d}" for x in args.chunks]
    else:
        ap.error("Specify --all or --chunks")

    wrote_any = False
    for cid in targets:
        primes = assign_for_chunk(cid, args.k)
        cid, merged, ok = update_chunk(base, cid, primes, write=args.write and not args.dry_run)
        status = "UPDATED" if args.write and not args.dry_run else "WOULD_UPDATE"
        if ok:
            print(f"{status} chunk-{cid}: monsterPrimes={merged}")
            wrote_any = wrote_any or (args.write and not args.dry_run)
        else:
            print(f"SKIP chunk-{cid}: constraints json not found")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
