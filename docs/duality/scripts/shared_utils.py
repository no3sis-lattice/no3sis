#!/usr/bin/env python3
"""
Shared utilities for duality formalization scripts.
Extracts common code to eliminate DRY violations.

Phase 3 Refactoring: Consolidates discover_chunks(), JSON loading, and CLI patterns.
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Callable


def discover_chunks(base_dir: Path) -> List[str]:
    """
    Discover all chunk IDs from JSON constraint files.

    Args:
        base_dir: Base duality directory (contains true-dual-tract/chunks/)

    Returns:
        List of chunk IDs as zero-padded strings (e.g., ["01", "06", "19"])
    """
    chunks_dir = base_dir / "true-dual-tract" / "chunks"

    if not chunks_dir.exists():
        return []

    ids = []
    for json_file in sorted(chunks_dir.glob("chunk-*.constraints.json")):
        match = re.search(r"chunk-(\d+)\.constraints\.json$", json_file.name)
        if match:
            ids.append(f"{int(match.group(1)):02d}")

    return ids


def load_json_safe(path: Path) -> Optional[Dict]:
    """
    Load JSON file with error handling.

    Args:
        path: Path to JSON file

    Returns:
        Parsed JSON dict, or None if error occurs
    """
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"Error: File not found: {path}", file=sys.stderr)
        return None
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {path}: {e}", file=sys.stderr)
        return None
    except Exception as e:
        print(f"Error reading {path}: {e}", file=sys.stderr)
        return None


def save_json_safe(path: Path, data: Dict) -> bool:
    """
    Save JSON file with error handling.

    Args:
        path: Path to JSON file
        data: Dictionary to save

    Returns:
        True if successful, False otherwise
    """
    try:
        json_str = json.dumps(data, indent=2, ensure_ascii=False)
        path.write_text(json_str, encoding="utf-8")
        return True
    except Exception as e:
        print(f"Error writing {path}: {e}", file=sys.stderr)
        return False


def get_chunk_json_path(chunk_id: str, base_dir: Path) -> Path:
    """
    Get path to chunk's JSON constraint file.

    Args:
        chunk_id: Chunk ID (e.g., "06" or "6")
        base_dir: Base duality directory

    Returns:
        Path to chunk-{id}.constraints.json
    """
    chunk_id_padded = f"{int(chunk_id):02d}"
    return base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id_padded}.constraints.json"


def get_chunk_mzn_path(chunk_id: str, base_dir: Path) -> Path:
    """
    Get path to chunk's MiniZinc model file.

    Args:
        chunk_id: Chunk ID (e.g., "06")
        base_dir: Base duality directory

    Returns:
        Path to chunk-{id}.mzn
    """
    chunk_id_padded = f"{int(chunk_id):02d}"
    return base_dir / "true-dual-tract" / "chunks" / f"chunk-{chunk_id_padded}.mzn"


def get_chunk_lean_path(chunk_id: str, base_dir: Path) -> Path:
    """
    Get path to chunk's Lean4 module file.

    Args:
        chunk_id: Chunk ID (e.g., "06")
        base_dir: Base duality directory

    Returns:
        Path to formal/Duality/Chunks/Chunk{id}.lean
    """
    chunk_id_padded = f"{int(chunk_id):02d}"
    return base_dir / "formal" / "Duality" / "Chunks" / f"Chunk{chunk_id_padded}.lean"


def add_common_cli_args(parser: argparse.ArgumentParser, default_base: Optional[Path] = None) -> None:
    """
    Add common CLI arguments to argument parser.

    Args:
        parser: ArgumentParser to add arguments to
        default_base: Default base directory (defaults to script's parent)
    """
    if default_base is None:
        # This will be overridden by caller if needed
        default_base = Path.cwd()

    parser.add_argument(
        "--base-dir",
        type=Path,
        default=default_base,
        help=f"Base duality directory (default: {default_base})"
    )
    parser.add_argument(
        "--chunk",
        type=str,
        help="Chunk ID to process (e.g., 06)"
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Process all discovered chunks"
    )


def process_chunks_batch(
    chunk_ids: List[str],
    process_func: Callable[[str, Path], bool],
    base_dir: Path,
    operation_name: str = "Processing"
) -> int:
    """
    Process multiple chunks with a given function.

    Args:
        chunk_ids: List of chunk IDs to process
        process_func: Function(chunk_id, base_dir) -> success:bool
        base_dir: Base duality directory
        operation_name: Name for progress messages

    Returns:
        Number of successfully processed chunks
    """
    if not chunk_ids:
        print(f"No chunks to process")
        return 0

    success_count = 0
    for cid in chunk_ids:
        try:
            if process_func(cid, base_dir):
                success_count += 1
        except Exception as e:
            print(f"Error processing chunk {cid}: {e}", file=sys.stderr)

    print(f"\n{operation_name}: {success_count}/{len(chunk_ids)} chunks successfully")
    return success_count


class ChunkProcessor:
    """
    Base class for chunk processors (transpilers, validators, etc.).

    Subclasses implement transform() to define specific processing logic.
    """

    def __init__(self, base_dir: Path):
        """
        Initialize processor.

        Args:
            base_dir: Base duality directory
        """
        self.base_dir = base_dir

    def load_chunk_json(self, chunk_id: str) -> Optional[Dict]:
        """Load chunk JSON data."""
        json_path = get_chunk_json_path(chunk_id, self.base_dir)
        return load_json_safe(json_path)

    def transform(self, chunk_id: str, chunk_data: Dict) -> Optional[str]:
        """
        Transform chunk data (to be implemented by subclasses).

        Args:
            chunk_id: Chunk ID
            chunk_data: Parsed JSON data

        Returns:
            Transformed output as string, or None if error
        """
        raise NotImplementedError("Subclasses must implement transform()")

    def get_output_path(self, chunk_id: str) -> Path:
        """
        Get output path for transformed chunk (to be implemented by subclasses).

        Args:
            chunk_id: Chunk ID

        Returns:
            Path to output file
        """
        raise NotImplementedError("Subclasses must implement get_output_path()")

    def process(self, chunk_id: str) -> bool:
        """
        Process a single chunk: load, transform, write.

        Args:
            chunk_id: Chunk ID

        Returns:
            True if successful, False otherwise
        """
        # Load
        chunk_data = self.load_chunk_json(chunk_id)
        if chunk_data is None:
            return False

        # Transform
        try:
            output = self.transform(chunk_id, chunk_data)
        except Exception as e:
            print(f"Error transforming chunk {chunk_id}: {e}", file=sys.stderr)
            return False

        if output is None:
            return False

        # Write
        output_path = self.get_output_path(chunk_id)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        try:
            output_path.write_text(output, encoding="utf-8")
            print(f"Generated: {output_path}")
            return True
        except Exception as e:
            print(f"Error writing {output_path}: {e}", file=sys.stderr)
            return False


def validate_chunk_id(chunk_id: str) -> str:
    """
    Validate and normalize chunk ID.

    Args:
        chunk_id: Raw chunk ID (e.g., "6", "06", "19")

    Returns:
        Zero-padded chunk ID (e.g., "06")

    Raises:
        ValueError: If chunk_id is invalid
    """
    try:
        num = int(chunk_id)
        if num < 1 or num > 99:
            raise ValueError(f"Chunk ID must be between 1 and 99, got: {chunk_id}")
        return f"{num:02d}"
    except ValueError as e:
        raise ValueError(f"Invalid chunk ID '{chunk_id}': {e}")


# ============================================================================
# Testing utilities
# ============================================================================

def create_test_chunk(chunk_id: str, title: str, constraints: List[Dict]) -> Dict:
    """
    Create a test chunk data structure.

    Args:
        chunk_id: Chunk ID
        title: Chunk title
        constraints: List of constraint dicts

    Returns:
        Valid chunk JSON structure
    """
    return {
        "id": chunk_id,
        "title": title,
        "parameters": {
            "scaleN": 100,
            "monsterPrimes": [2, 3, 5, 7, 11, 13, 17, 19]
        },
        "constraints": constraints
    }


if __name__ == "__main__":
    # Quick self-test
    print("shared_utils.py - Common utilities for duality scripts")
    print(f"Functions available: {[f for f in dir() if not f.startswith('_') and callable(globals()[f])]}")
