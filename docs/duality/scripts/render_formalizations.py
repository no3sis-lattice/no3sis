#!/usr/bin/env python3
"""
Render MiniZinc (.mzn) and Lean4 (.lean) files from a chunk constraints JSON.

Usage:
  python scripts/duality/render_formalizations.py path/to/chunk-NN.constraints.json
"""
from __future__ import annotations
import argparse, json, re
from pathlib import Path

MZN_TPL = (Path(__file__).parent.parent / "templates" / "chunk.mzn").read_text()
LEAN_TPL = (Path(__file__).parent.parent / "templates" / "chunk.lean").read_text()

def render_constraints_to_mzn(constraints: list[dict]) -> str:
    # Naive passthrough: assume expr contains valid MiniZinc fragments
    lines = []
    for c in constraints:
        lines.append(f"% constraint: {c.get('name','')}")
        lines.append(f"constraint {c['expr']};")
    return "\n".join(lines)

def render_constraints_to_lean(constraints: list[dict]) -> str:
    # Naive placeholder: join as True ∧ True ... for now
    if not constraints:
        return "True"
    props = " ∧ ".join([ "(" + (c["expr"]) + ")" for c in constraints ])
    # In practice, translate DSL to Lean propositions here.
    return props

def main():
    ap = argparse.ArgumentParser(description="Render MiniZinc and Lean4 files from JSON constraints")
    ap.add_argument("json_path", type=Path, help="Path to chunk-NN.constraints.json")
    ap.add_argument("--output-dir", type=Path, default=None,
                    help="Output directory (default: formal/Duality/Chunks relative to json_path)")
    ap.add_argument("--also-to-chunks", action="store_true",
                    help="Also write to chunks/ directory for reference")
    ap.add_argument("--force", action="store_true",
                    help="Overwrite existing files (default: preserve existing Lean proofs)")
    args = ap.parse_args()

    data = json.loads(args.json_path.read_text())
    nn = data["id"]
    scale = data.get("parameters", {}).get("scaleN", 100)
    primes = data.get("parameters", {}).get("monsterPrimes", [2,3,5,7,11,13,17,19])

    mzn_constraints = render_constraints_to_mzn(data["constraints"])
    lean_constraints = render_constraints_to_lean(data["constraints"])

    mzn = (MZN_TPL
           .replace("{{SCALE_N}}", str(scale))
           .replace("{{MONSTER_PRIME_SET}}", ", ".join(str(p) for p in primes))
           .replace("{{CONSTRAINTS}}", mzn_constraints or "% none")
           .replace("{{OBJECTIVE}}", "% none"))

    lean = (LEAN_TPL
            .replace("ChunkNN", f"Chunk{nn}")
            .replace("{{SCALE_N}}", str(scale))
            .replace("{{DOMAIN_CONSTRAINTS}}", lean_constraints))

    # Determine output directory
    if args.output_dir:
        out_dir = args.output_dir
    else:
        # Default: formal/Duality/Chunks (3 levels up from json_path, then into formal/)
        base_duality_dir = args.json_path.parents[2]  # From chunks/chunk-NN.json up to duality/
        out_dir = base_duality_dir / "formal" / "Duality" / "Chunks"

    out_dir.mkdir(parents=True, exist_ok=True)

    # Write to formal/ directory (primary output)
    lean_path = out_dir / f"Chunk{nn}.lean"
    mzn_path = out_dir / f"Chunk{nn}.mzn"

    # Always write MZN (constraint changes)
    mzn_path.write_text(mzn)
    print(f"Rendered: {mzn_path}")

    # Preserve existing Lean proofs unless --force
    if lean_path.exists() and not args.force:
        print(f"Preserved existing Lean proof: {lean_path} (use --force to overwrite)")
    else:
        lean_path.write_text(lean)
        print(f"Rendered: {lean_path}")

    # Optionally also write to chunks/ for reference
    if args.also_to_chunks:
        chunks_dir = args.json_path.parent
        (chunks_dir / f"chunk-{nn}.mzn").write_text(mzn)
        (chunks_dir / f"chunk-{nn}.lean").write_text(lean)
        print(f"Also copied to: {chunks_dir / f'chunk-{nn}.mzn'}")
        print(f"Also copied to: {chunks_dir / f'chunk-{nn}.lean'}")

if __name__ == "__main__":
    main()
