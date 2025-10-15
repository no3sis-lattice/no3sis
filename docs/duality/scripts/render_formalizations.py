#!/usr/bin/env python3
"""
Render MiniZinc (.mzn) and Lean4 (.lean) files from a chunk constraints JSON.

Phase 6b: Unified with real transpiler logic from transpile_to_lean.py
Phase 6b Hotfix: Support base import mode for existing Duality project
Phase 2: Doc chunk handling - schema validation only for doc chunks
Phase 2.1: Import shared utilities (DRY refactor)

Usage:
  python scripts/duality/render_formalizations.py path/to/chunk-NN.constraints.json
  python scripts/duality/render_formalizations.py path/to/chunk-NN.constraints.json --use-base-imports
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path
from typing import Set

# Import real transpilers (Phase 6b unification)
from transpile_to_mzn import generate_mzn_from_json
from transpile_to_lean import generate_lean_from_json

# Phase 2.1: Import shared utilities
from shared_utils import load_doc_chunks

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
    ap.add_argument("--with-ipv6", action="store_true",
                    help="[Phase 5] Include IPv6 encoding for Chunk 06 (pilot demo, OFF by default)")
    args = ap.parse_args()

    # Load JSON data
    data = json.loads(args.json_path.read_text())
    chunk_id = data["id"]
    goal_type = data.get("goalType", "refinement")

    # Phase 2: Check if this is a doc chunk
    base_duality_dir = args.json_path.parents[2]  # From chunks/chunk-NN.json up to duality/
    doc_chunks = load_doc_chunks(base_duality_dir)
    is_doc_chunk = chunk_id in doc_chunks

    # Phase 2: Doc chunks get schema validation only (skip transpilation)
    if is_doc_chunk:
        print(f"✓ Doc chunk {chunk_id}: Schema validated (skipping transpilation)")
        print(f"  Title: {data.get('title', 'N/A')}")
        print(f"  Type: {goal_type}")
        print(f"  Constraints: {len(data.get('constraints', []))} defined")
        return 0

    # Skip MiniZinc for documentation/proof chunks (architectural decision)
    # Proof chunks use Lean for formal verification, not MiniZinc for constraint solving
    # EXCEPTION: Phase 5 IPv6 demo for Chunk 06 forces MZN generation when flag enabled
    should_generate_mzn = goal_type in ["search", "refinement"]

    # Phase 5: Force MZN generation for Chunk 06 when IPv6 demo enabled
    if args.with_ipv6 and chunk_id == "06":
        should_generate_mzn = True
        print(f"[Phase 5 IPv6 Demo] Forcing MZN generation for Chunk 06")

    # Generate using real transpilers (Phase 6b)
    if should_generate_mzn:
        # Phase 5: Pass IPv6 flag and chunk_id to transpiler
        mzn_content = generate_mzn_from_json(data, with_ipv6=args.with_ipv6, chunk_id=chunk_id)
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
    sys.exit(main())
