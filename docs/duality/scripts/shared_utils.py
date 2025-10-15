#!/usr/bin/env python3
"""
Shared utility functions for duality scripts.
Phase 2.1: DRY refactor - centralized doc chunk loading.
"""
from __future__ import annotations
import json
from pathlib import Path
from typing import Set


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
