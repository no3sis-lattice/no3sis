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
        lines.append(f"% {c.get('name','')}")
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
    ap = argparse.ArgumentParser()
    ap.add_argument("json_path", type=Path)
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

    out_dir = args.json_path.parent
    (out_dir / f"chunk-{nn}.mzn").write_text(mzn)
    (out_dir / f"chunk-{nn}.lean").write_text(lean)
    print(f"Rendered: {out_dir / f'chunk-{nn}.mzn'}")
    print(f"Rendered: {out_dir / f'chunk-{nn}.lean'}")

if __name__ == "__main__":
    main()
