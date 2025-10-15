#!/usr/bin/env python3
"""
Shared utility functions for duality scripts.
Phase 2.1: DRY refactor - centralized doc chunk loading.
Phase 5.5: Added missing utilities for transpiler CLI functions.
"""
from __future__ import annotations
import json
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set


def load_doc_chunks(base_dir: Path) -> Set[str]:
    """
    Load documentation chunk IDs from doc_chunks.json.

    Args:
        base_dir: Base duality directory (docs/duality)

    Returns:
        Set of chunk IDs as zero-padded strings (e.g., {"01", "02", "05"})

    Example:
        >>> from pathlib import Path
        >>> base = Path("/home/user/synapse/docs/duality")
        >>> doc_chunks = load_doc_chunks(base)
        >>> "01" in doc_chunks
        True
    """
    doc_chunks_file = base_dir / "doc_chunks.json"

    # Return empty set if file doesn't exist (graceful degradation)
    if not doc_chunks_file.exists():
        return set()

    try:
        data = json.loads(doc_chunks_file.read_text(encoding="utf-8"))
        raw_chunks = data.get("doc_chunks", [])

        # Ensure zero-padding for consistency (handles both "1" and "01" inputs)
        return {f"{int(cid):02d}" for cid in raw_chunks}

    except (json.JSONDecodeError, ValueError, KeyError) as e:
        # Log error but don't crash - return empty set
        # Caller can decide how to handle empty doc chunks
        return set()


def get_base_duality_dir(script_path: Path) -> Path:
    """
    Compute base duality directory from script location.

    Assumes scripts live in docs/duality/scripts/, so base is 1 level up.

    Args:
        script_path: Path to the calling script (usually __file__)

    Returns:
        Path to docs/duality directory

    Example:
        >>> from pathlib import Path
        >>> script = Path("/home/user/synapse/docs/duality/scripts/cross_check_all.py")
        >>> get_base_duality_dir(script)
        PosixPath('/home/user/synapse/docs/duality')
    """
    return script_path.resolve().parent.parent


def discover_chunks(base_dir: Path) -> List[str]:
    """
    Discover chunk IDs by scanning for files named chunk-XX.constraints.json
    in <base_dir>/true-dual-tract/chunks.

    Args:
        base_dir: Base duality directory (docs/duality)

    Returns:
        Sorted list of zero-padded chunk IDs as strings (e.g., ["01", "06", "08"])

    Example:
        >>> from pathlib import Path
        >>> base = Path("/home/user/synapse/docs/duality")
        >>> chunks = discover_chunks(base)
        >>> "06" in chunks
        True
    """
    chunks_dir = base_dir / "true-dual-tract" / "chunks"
    if not chunks_dir.exists():
        return []

    chunk_ids = set()
    for file in chunks_dir.glob("chunk-*.constraints.json"):
        # Extract the chunk ID from filename like "chunk-06.constraints.json"
        stem = file.stem  # e.g., "chunk-06.constraints"
        parts = stem.split("-")
        if len(parts) >= 2:
            # Get the numeric part before ".constraints"
            chunk_id = parts[1].split(".")[0]
            try:
                # Zero-pad for consistency
                chunk_ids.add(f"{int(chunk_id):02d}")
            except ValueError:
                pass  # Skip malformed filenames

    return sorted(chunk_ids)


def get_chunk_json_path(chunk_id: str, base_dir: Path) -> Path:
    """
    Get path to chunk JSON file.

    Args:
        chunk_id: Zero-padded chunk ID (e.g., "06")
        base_dir: Base duality directory

    Returns:
        Path to chunk-XX.constraints.json
    """
    return base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id}.constraints.json"


def get_chunk_lean_path(chunk_id: str, base_dir: Path) -> Path:
    """
    Get path to chunk Lean4 output file.

    Args:
        chunk_id: Zero-padded chunk ID (e.g., "06")
        base_dir: Base duality directory

    Returns:
        Path to formal/Duality/Chunks/ChunkXX.lean
    """
    return base_dir / "formal" / "Duality" / "Chunks" / f"Chunk{chunk_id}.lean"


def get_chunk_mzn_path(chunk_id: str, base_dir: Path) -> Path:
    """
    Get path to chunk MiniZinc output file.

    Args:
        chunk_id: Zero-padded chunk ID (e.g., "06")
        base_dir: Base duality directory

    Returns:
        Path to true-dual-tract/chunks/chunk-XX.mzn
    """
    return base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id}.mzn"


def load_json_safe(path: Path) -> Optional[Dict]:
    """
    Safely load JSON file with error handling.

    Args:
        path: Path to JSON file

    Returns:
        Parsed JSON dict, or None if file doesn't exist or is invalid
    """
    if not path.exists():
        print(f"Error: File not found: {path}", file=sys.stderr)
        return None

    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {path}: {e}", file=sys.stderr)
        return None
    except Exception as e:
        print(f"Error reading {path}: {e}", file=sys.stderr)
        return None


def save_json_safe(path: Path, data: Dict) -> bool:
    """
    Safely write JSON file with error handling.

    Args:
        path: Path to write JSON file
        data: Dictionary to serialize

    Returns:
        True if successful, False otherwise
    """
    try:
        # Ensure parent directory exists
        path.parent.mkdir(parents=True, exist_ok=True)

        # Write with pretty formatting
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        return True
    except Exception as e:
        print(f"Error writing {path}: {e}", file=sys.stderr)
        return False


# For interactive use / testing
if __name__ == "__main__":
    import sys

    # Test from current script location
    base = get_base_duality_dir(Path(__file__))
    print(f"Base duality directory: {base}")

    doc_chunks = load_doc_chunks(base)
    print(f"Doc chunks loaded: {sorted(doc_chunks)}")
    print(f"Total: {len(doc_chunks)}")

    if not doc_chunks:
        print("Warning: No doc chunks found. Check doc_chunks.json exists.", file=sys.stderr)
        sys.exit(1)
