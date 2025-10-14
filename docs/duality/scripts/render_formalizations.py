#!/usr/bin/env python3
"""
Render MiniZinc (.mzn) and Lean4 (.lean) files from a chunk constraints JSON.

Phase 6b: Unified with real transpiler logic from transpile_to_lean.py
Phase 6b Hotfix: Support base import mode for existing Duality project

Usage:
  python scripts/duality/render_formalizations.py path/to/chunk-NN.constraints.json
  python scripts/duality/render_formalizations.py path/to/chunk-NN.constraints.json --use-base-imports
"""
from __future__ import annotations
import argparse, json, re
from pathlib import Path

# Import real transpilers (Phase 6b unification)
from transpile_to_mzn import generate_mzn_from_json
from transpile_to_lean import generate_lean_from_json

def main():
    ap = argparse.ArgumentParser(description="Render MiniZinc and Lean4 files from JSON constraints")
    ap.add_argument("json_path", type=Path, help="Path to chunk-NN.constraints.json")
    ap.add_argument("--output-dir", type=Path, default=None,
                    help="Output directory (default: formal/Duality/Chunks relative to json_path)")
    ap.add_argument("--also-to-chunks", action="store_true",
                    help="Also write to chunks/ directory for reference")
    ap.add_argument("--force", action="store_true",
                    help="Overwrite existing files (default: preserve existing Lean proofs)")
    ap.add_argument("--use-base-imports", action="store_true",
                    help="Generate Lean with Duality.Base imports (for existing project) instead of inline definitions")
    args = ap.parse_args()

    # Load JSON data
    data = json.loads(args.json_path.read_text())
    chunk_id = data["id"]
    goal_type = data.get("goalType", "refinement")

    # Skip MiniZinc for documentation/proof chunks (architectural decision)
    # Proof chunks use Lean for formal verification, not MiniZinc for constraint solving
    should_generate_mzn = goal_type in ["search", "refinement"]

    # Generate using real transpilers (Phase 6b)
    if should_generate_mzn:
        mzn_content = generate_mzn_from_json(data)
    else:
        print(f"Skipping MiniZinc for chunk {chunk_id} (goalType: {goal_type})")
        mzn_content = None

    lean_content = generate_lean_from_json(data, use_base_imports=args.use_base_imports)

    # Determine output directory
    if args.output_dir:
        out_dir = args.output_dir
    else:
        # Default: formal/Duality/Chunks (3 levels up from json_path, then into formal/)
        base_duality_dir = args.json_path.parents[2]  # From chunks/chunk-NN.json up to duality/
        out_dir = base_duality_dir / "formal" / "Duality" / "Chunks"

    out_dir.mkdir(parents=True, exist_ok=True)

    # Write to formal/ directory (primary output)
    lean_path = out_dir / f"Chunk{chunk_id}.lean"
    mzn_path = out_dir / f"Chunk{chunk_id}.mzn"

    # Write MZN only if generated (skip for goalType: proof)
    if mzn_content:
        mzn_path.write_text(mzn_content)
        print(f"Rendered: {mzn_path}")

    # Preserve existing Lean proofs unless --force
    if lean_path.exists() and not args.force:
        print(f"Preserved existing Lean proof: {lean_path} (use --force to overwrite)")
    else:
        lean_path.write_text(lean_content)
        print(f"Rendered: {lean_path}")

    # Optionally also write to chunks/ for reference
    if args.also_to_chunks:
        chunks_dir = args.json_path.parent
        if mzn_content:
            (chunks_dir / f"chunk-{chunk_id}.mzn").write_text(mzn_content)
            print(f"Also copied to: {chunks_dir / f'chunk-{chunk_id}.mzn'}")
        (chunks_dir / f"chunk-{chunk_id}.lean").write_text(lean_content)
        print(f"Also copied to: {chunks_dir / f'chunk-{chunk_id}.lean'}")

if __name__ == "__main__":
    main()
