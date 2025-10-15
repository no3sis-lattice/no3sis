#!/usr/bin/env python3
"""
Phase 3: Numogrammatic Monster Prime Assignment

Assigns Monster group prime factors to chunks deterministically using Blake2b hashing.

Features:
- Blake2b stable hash (deterministic across machines)
- Tract-biased selection (internal=odd-prefer, external=2+odd, bridge=balanced)
- Lemurian zone (chunk_id % 10) incorporated into seed
- k=3 primes per chunk (configurable)

Usage:
  python assign_monster_primes.py --all --k 3 --write
  python assign_monster_primes.py --chunks 06 09 19 --k 3 --write
  python assign_monster_primes.py --dry-run --chunks 06
  python assign_monster_primes.py --all --k 3 --write --exclude-doc-chunks
"""
from __future__ import annotations
import argparse, json, re, hashlib
from pathlib import Path
from typing import Literal

MONSTER_PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
MONSTER_PRIMES_ODD = [3,5,7,11,13,17,19,23,29,31,41,47,59,71]  # Exclude 2
MONSTER_PRIMES_EVEN_ODD = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]  # All (same as MONSTER_PRIMES)

TractType = Literal["internal", "external", "bridge", "unknown"]

def discover_chunks(base_dir: Path) -> list[str]:
    chunks_dir = base_dir / "true-dual-tract" / "chunks"
    ids = []
    for p in sorted(chunks_dir.glob("chunk-*.constraints.json")):
        m = re.search(r"chunk-(\d+)\.constraints\.json$", p.name)
        if m:
            ids.append(f"{int(m.group(1)):02d}")
    return ids

def infer_tract(chunk_path: Path) -> TractType:
    """Infer tract type from chunk title or heuristics."""
    try:
        data = json.loads(chunk_path.read_text(encoding="utf-8"))
        title = data.get("title", "").lower()

        if "external tract" in title or "interface operator" in title:
            return "external"
        elif "internal tract" in title or "intelligence operator" in title:
            return "internal"
        elif "bridge" in title or "corpus callosum" in title:
            return "bridge"
        else:
            # Heuristic: Use Lemurian zone (chunk_id % 10)
            cid = int(data.get("id", "0"))
            zone = cid % 10
            if zone <= 3:
                return "internal"
            elif zone <= 6:
                return "external"
            else:
                return "bridge"
    except Exception:
        return "unknown"

def assign_for_chunk(cid: str, k: int, base_dir: Path) -> list[int]:
    """
    Assign k Monster primes to chunk using Blake2b hash.

    Incorporates:
    - Chunk ID
    - Lemurian zone (chunk_id % 10)
    - Tract bias (internal=odd-prefer, external=2+odd, bridge=balanced)
    """
    chunk_int = int(cid)
    lemurian_zone = chunk_int % 10

    # Infer tract type
    chunk_path = base_dir / "true-dual-tract" / "chunks" / f"chunk-{cid}.constraints.json"
    tract = infer_tract(chunk_path)

    # Select prime pool based on tract bias
    if tract == "internal":
        # Internal: prefer odd primes (exclude 2)
        prime_pool = MONSTER_PRIMES_ODD
    elif tract == "external":
        # External: include 2 + odd (all primes)
        prime_pool = MONSTER_PRIMES_EVEN_ODD
    else:
        # Bridge/unknown: balanced (all primes)
        prime_pool = MONSTER_PRIMES

    # Create deterministic seed: chunk_id + lemurian_zone
    seed_str = f"chunk:{cid}:zone:{lemurian_zone}:tract:{tract}"
    seed_hash = hashlib.blake2b(seed_str.encode('utf-8'), digest_size=16).digest()

    # Convert hash to integers and select k primes deterministically
    picks = []
    pool_size = len(prime_pool)
    for i in range(k):
        # Use different bytes from hash for each selection
        offset = i * 2
        if offset + 1 < len(seed_hash):
            # Combine two bytes for better distribution
            idx = (seed_hash[offset] * 256 + seed_hash[offset + 1]) % pool_size
        else:
            # Fallback for small hash
            idx = seed_hash[offset % len(seed_hash)] % pool_size

        prime = prime_pool[idx]
        picks.append(prime)

        # Remove from pool to avoid duplicates
        prime_pool = [p for p in prime_pool if p != prime]
        pool_size = len(prime_pool)

        # If pool exhausted, break early
        if pool_size == 0:
            break

    return sorted(set(picks))

def update_chunk(base_dir: Path, cid: str, primes: list[int], write: bool, replace: bool = True) -> tuple[str, list[int], bool, str]:
    """
    Update chunk's monsterPrimes field.

    Args:
        base_dir: Base duality directory
        cid: Chunk ID (zero-padded string)
        primes: List of primes to assign
        write: Actually write to file
        replace: If True, replace existing primes; if False, merge with existing

    Returns:
        (cid, final_primes, success, tract_type)
    """
    path = base_dir / "true-dual-tract" / "chunks" / f"chunk-{cid}.constraints.json"
    if not path.exists():
        return (cid, [], False, "missing")

    data = json.loads(path.read_text(encoding="utf-8"))
    params = data.setdefault("parameters", {})
    tract = infer_tract(path)

    if replace:
        # Phase 3: Replace existing primes with new assignment
        final_primes = sorted(primes)
    else:
        # Legacy: Merge with existing primes
        existing = params.get("monsterPrimes", [])
        final_primes = sorted(set(map(int, existing)) | set(primes))

    params["monsterPrimes"] = final_primes

    if write:
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    return (cid, final_primes, True, tract)

def main():
    ap = argparse.ArgumentParser(description="Phase 3: Numogrammatic Monster Prime Assignment")
    ap.add_argument("--all", action="store_true", help="Process all discovered chunks")
    ap.add_argument("--chunks", nargs="+", help="Specific chunk IDs (e.g., 06 09 19)")
    ap.add_argument("--k", type=int, default=3, help="Number of primes to assign per chunk (default: 3)")
    ap.add_argument("--write", action="store_true", help="Write changes to files (otherwise dry run)")
    ap.add_argument("--dry-run", action="store_true", help="Alias for default (no write)")
    ap.add_argument("--exclude-doc-chunks", action="store_true", help="Exclude documentation chunks from assignment")
    ap.add_argument("--exclude-pilot", type=str, help="Exclude specific pilot chunk (e.g., '41')")
    ap.add_argument("--replace", action="store_true", default=True, help="Replace existing primes (default)")
    ap.add_argument("--merge", action="store_true", help="Merge with existing primes instead of replacing")
    args = ap.parse_args()

    base = Path(__file__).resolve().parents[1]
    targets = []

    # Discover target chunks
    if args.all:
        targets = discover_chunks(base)
    elif args.chunks:
        targets = [f"{int(x):02d}" for x in args.chunks]
    else:
        ap.error("Specify --all or --chunks")

    # Load doc chunks if exclusion requested
    doc_chunks = set()
    if args.exclude_doc_chunks:
        try:
            from shared_utils import load_doc_chunks
            doc_chunks = load_doc_chunks(base)
        except Exception:
            # Fallback: load directly
            doc_chunks_file = base / "doc_chunks.json"
            if doc_chunks_file.exists():
                data = json.loads(doc_chunks_file.read_text(encoding="utf-8"))
                doc_chunks = {f"{int(cid):02d}" for cid in data.get("doc_chunks", [])}

    # Exclude doc chunks and pilot
    excluded = set()
    if args.exclude_doc_chunks:
        excluded |= doc_chunks
    if args.exclude_pilot:
        excluded.add(f"{int(args.exclude_pilot):02d}")

    targets = [cid for cid in targets if cid not in excluded]

    # Process chunks
    replace_mode = not args.merge  # Default is replace unless --merge specified
    wrote_any = False
    tract_counts = {"internal": 0, "external": 0, "bridge": 0, "unknown": 0}

    print(f"Phase 3: Numogrammatic Monster Prime Assignment")
    print(f"  Targets: {len(targets)} chunks (k={args.k}, mode={'REPLACE' if replace_mode else 'MERGE'})")
    if excluded:
        print(f"  Excluded: {sorted(excluded)}")
    print()

    for cid in targets:
        primes = assign_for_chunk(cid, args.k, base)
        cid, final_primes, ok, tract = update_chunk(base, cid, primes, write=args.write and not args.dry_run, replace=replace_mode)
        status = "UPDATED" if args.write and not args.dry_run else "PREVIEW"

        if ok:
            tract_counts[tract] = tract_counts.get(tract, 0) + 1
            print(f"{status} chunk-{cid} [{tract:>8}]: {final_primes}")
            wrote_any = wrote_any or (args.write and not args.dry_run)
        else:
            print(f"SKIP chunk-{cid}: constraints json not found")

    # Summary
    print()
    print(f"Summary:")
    print(f"  Total processed: {sum(tract_counts.values())} chunks")
    print(f"  Internal tract: {tract_counts['internal']} chunks (odd-prefer)")
    print(f"  External tract: {tract_counts['external']} chunks (2+odd)")
    print(f"  Bridge tract: {tract_counts['bridge']} chunks (balanced)")
    print(f"  Unknown tract: {tract_counts['unknown']} chunks (balanced)")
    print(f"  Status: {'WRITTEN TO DISK' if wrote_any else 'DRY RUN (use --write to apply)'}")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
