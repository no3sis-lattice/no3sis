#!/usr/bin/env python3
"""
Constraint Injection Script for Phase 3 De-Trivialization
Adds 2-3 meaningful constraints to INSUFFICIENT chunks based on templates

Usage:
  python3 add_constraints.py --chunk 01
  python3 add_constraints.py --all
  python3 add_constraints.py --chunk 01 --dry-run
"""

import argparse
import json
import random
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Import shared utilities (Phase 2.1)
from shared_utils import (
    load_json_safe,
    save_json_safe,
    get_chunk_json_path,
)


def load_templates(template_path: Path) -> Dict:
    """Load constraint templates from JSON file."""
    result = load_json_safe(template_path)
    if result is None:
        raise ValueError(f"Failed to load templates from {template_path}")
    return result


def detect_chunk_type(chunk_data: Dict) -> str:
    """
    Detect chunk type from title/id for heuristic selection.

    Returns: 'external', 'internal', 'bridge', 'boss', or 'default'
    """
    title = chunk_data.get("title", "").lower()
    chunk_id = chunk_data.get("id", "")

    # Heuristics based on title keywords
    if "external" in title or "interface" in title or "operator" in title:
        return "external"
    elif "internal" in title or "self" in title or "planning" in title:
        return "internal"
    elif "bridge" in title or "corpus" in title or "callosum" in title:
        return "bridge"
    elif "boss" in title or "orchestr" in title or chunk_id == "19":
        return "boss"
    else:
        return "default"


def count_existing_constraints(chunk_data: Dict) -> int:
    """Count non-trivial existing constraints."""
    constraints = chunk_data.get("constraints", [])
    non_trivial = 0
    for c in constraints:
        expr = c.get("expr", "true").strip().lower()
        # Skip trivial constraints (true, or existence markers)
        if expr not in ("true", "false") and "exists" not in c.get("name", ""):
            non_trivial += 1
    return non_trivial


def generate_constraint_from_template(
    template: Dict,
    param_suggestions: Dict,
    chunk_id: str,
    existing_names: List[str]
) -> Dict:
    """
    Generate a constraint instance from a template.

    Returns: {"name": "...", "expr": "...", "notes": "..."}
    """
    template_id = template["id"]
    json_expr = template["json_expr"]
    description = template["description"]
    params = template["params"]

    # Fill in parameters
    instantiated_expr = json_expr
    name_parts = [template_id]

    for param in params:
        if param in param_suggestions:
            value = param_suggestions[param]
            instantiated_expr = instantiated_expr.replace(f"{{{param}}}", str(value))
            if param in ("dim", "dim1", "dim2", "start", "end"):
                name_parts.append(f"{param}{value}")
        else:
            # Generate reasonable default if not provided
            if param == "dim":
                value = random.randint(1, 8)
            elif param in ("min", "floor", "threshold", "trigger_val", "dep_val"):
                value = random.choice([1, 3, 5, 10])
            elif param in ("max", "ceiling"):
                value = random.choice([20, 30, 40, 50])
            elif param == "tolerance":
                value = random.choice([5, 10, 15, 20])
            elif param == "prime":
                value = random.choice([2, 3, 5, 7])
            elif param in ("start", "dim1", "trigger_dim"):
                value = random.randint(1, 4)
            elif param in ("end", "dim2", "dep_dim", "dom_dim", "sub_dim"):
                value = random.randint(5, 8)
            elif param in ("max_nonzero", "min_nonzero", "min_each"):
                value = random.randint(2, 5)
            elif param in ("threshold1", "threshold2"):
                value = random.randint(5, 15)
            else:
                value = 1  # Fallback

            instantiated_expr = instantiated_expr.replace(f"{{{param}}}", str(value))
            if param in ("dim", "dim1", "dim2", "start", "end"):
                name_parts.append(f"{param}{value}")

    # Generate unique name
    base_name = "_".join(name_parts)
    name = base_name
    counter = 1
    while name in existing_names:
        name = f"{base_name}_{counter}"
        counter += 1

    return {
        "name": name,
        "expr": instantiated_expr,
        "notes": f"PHASE3: {description}"
    }


def add_constraints_to_chunk(
    chunk_data: Dict,
    templates_data: Dict,
    target_count: int = 2
) -> Tuple[Dict, int]:
    """
    Add constraints to a chunk to reach target_count non-trivial constraints.

    Returns: (updated_chunk_data, num_added)
    """
    chunk_id = chunk_data.get("id", "XX")
    chunk_type = detect_chunk_type(chunk_data)

    # Get heuristics for this chunk type
    heuristics = templates_data["chunk_heuristics"].get(chunk_type, templates_data["chunk_heuristics"]["default"])
    preferred_template_ids = heuristics["preferred_templates"]
    param_suggestions_map = heuristics["param_suggestions"]

    # Get existing constraint names
    existing_constraints = chunk_data.get("constraints", [])
    existing_names = [c.get("name", "") for c in existing_constraints]
    non_trivial_count = count_existing_constraints(chunk_data)

    # Calculate how many to add
    needed = max(0, target_count - non_trivial_count)
    if needed == 0:
        return chunk_data, 0

    # Build list of available templates
    all_templates = templates_data["templates"]
    template_map = {t["id"]: t for t in all_templates}

    # Prioritize preferred templates
    templates_to_use = []
    for tid in preferred_template_ids:
        if tid in template_map and len(templates_to_use) < needed:
            templates_to_use.append(template_map[tid])

    # Fill remaining with random templates if needed
    if len(templates_to_use) < needed:
        remaining_templates = [t for t in all_templates if t["id"] not in preferred_template_ids]
        random.shuffle(remaining_templates)
        templates_to_use.extend(remaining_templates[:needed - len(templates_to_use)])

    # Generate new constraints
    new_constraints = []
    for template in templates_to_use[:needed]:
        param_suggestions = param_suggestions_map.get(template["id"], {})
        constraint = generate_constraint_from_template(
            template,
            param_suggestions,
            chunk_id,
            existing_names
        )
        new_constraints.append(constraint)
        existing_names.append(constraint["name"])

    # Add to chunk data
    updated_chunk_data = chunk_data.copy()
    updated_chunk_data["constraints"] = existing_constraints + new_constraints

    return updated_chunk_data, len(new_constraints)


def process_chunk(
    chunk_id: str,
    base_dir: Path,
    templates_data: Dict,
    target_count: int = 2,
    dry_run: bool = False
) -> bool:
    """Process a single chunk and add constraints if needed."""
    # Load JSON using shared utility
    json_path = get_chunk_json_path(chunk_id, base_dir)
    chunk_data = load_json_safe(json_path)

    if chunk_data is None:
        return False

    # Check current status
    non_trivial = count_existing_constraints(chunk_data)
    if non_trivial >= target_count:
        print(f"Chunk {chunk_id}: Already has {non_trivial} constraints (target: {target_count}) - skipping")
        return True

    # Add constraints
    updated_chunk_data, num_added = add_constraints_to_chunk(chunk_data, templates_data, target_count)

    if num_added == 0:
        print(f"Chunk {chunk_id}: No constraints added")
        return True

    # Report
    chunk_type = detect_chunk_type(chunk_data)
    print(f"Chunk {chunk_id} ({chunk_type}): Added {num_added} constraints ({non_trivial} → {non_trivial + num_added})")

    if dry_run:
        print(f"  [DRY-RUN] Would write to: {json_path}")
        for c in updated_chunk_data["constraints"][-num_added:]:
            print(f"    + {c['name']}: {c['expr']}")
        return True

    # Write back using shared utility
    if save_json_safe(json_path, updated_chunk_data):
        print(f"  Updated: {json_path}")
        return True
    else:
        return False


def discover_insufficient_chunks(base_dir: Path, target_count: int = 2) -> List[str]:
    """Discover chunks with fewer than target_count non-trivial constraints."""
    chunks_dir = base_dir / "true-dual-tract" / "chunks"
    insufficient = []

    for json_file in sorted(chunks_dir.glob("chunk-*.constraints.json")):
        match = re.search(r"chunk-(\d+)\.constraints\.json$", json_file.name)
        if not match:
            continue

        chunk_id = f"{int(match.group(1)):02d}"
        chunk_data = json.loads(json_file.read_text(encoding="utf-8"))
        non_trivial = count_existing_constraints(chunk_data)

        if non_trivial < target_count:
            insufficient.append(chunk_id)

    return insufficient


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Add constraints to INSUFFICIENT chunks for Phase 3"
    )

    default_base = Path(__file__).resolve().parents[1]
    parser.add_argument(
        "--base-dir",
        type=Path,
        default=default_base,
        help=f"Base duality directory (default: {default_base})"
    )
    parser.add_argument(
        "--chunk",
        type=str,
        help="Chunk ID to process (e.g., 01)"
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Process all INSUFFICIENT chunks"
    )
    parser.add_argument(
        "--target-count",
        type=int,
        default=2,
        help="Target number of non-trivial constraints per chunk (default: 2)"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be added without modifying files"
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="Random seed for reproducibility (default: 42)"
    )

    args = parser.parse_args(argv)

    if not args.chunk and not args.all:
        parser.error("Must specify --chunk or --all")

    # Set random seed for reproducibility
    random.seed(args.seed)

    base_dir = args.base_dir
    templates_path = base_dir / "constraint_templates.json"

    if not templates_path.exists():
        print(f"Error: Template file not found: {templates_path}", file=sys.stderr)
        return 1

    # Load templates
    templates_data = load_templates(templates_path)

    if args.all:
        chunk_ids = discover_insufficient_chunks(base_dir, args.target_count)
        if not chunk_ids:
            print("No INSUFFICIENT chunks found")
            return 0

        print(f"Found {len(chunk_ids)} INSUFFICIENT chunks to process")
        if args.dry_run:
            print("[DRY-RUN MODE]")
        print()

        success_count = 0
        for cid in chunk_ids:
            if process_chunk(cid, base_dir, templates_data, args.target_count, args.dry_run):
                success_count += 1

        print(f"\nProcessed {success_count}/{len(chunk_ids)} chunks successfully")
        return 0 if success_count == len(chunk_ids) else 1

    else:
        # Process single chunk
        chunk_id = f"{int(args.chunk):02d}"
        if args.dry_run:
            print("[DRY-RUN MODE]")
        success = process_chunk(chunk_id, base_dir, templates_data, args.target_count, args.dry_run)
        return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
