#!/usr/bin/env python3
"""
CI Script: Validate JSON constraint files against schema
Extracted from inline workflow script for DRY compliance
"""

import json
import jsonschema
import sys
from pathlib import Path
from typing import List, Optional


def validate_pilot_chunks(pilots: List[str]) -> int:
    """Validate specific pilot chunks against schema."""
    schema = json.loads(Path('templates/chunk-constraints.schema.json').read_text())
    errors = []
    success = 0

    for pilot_id in pilots:
        f = Path(f'true-dual-tract/chunks/chunk-{pilot_id}.constraints.json')
        try:
            data = json.loads(f.read_text())
            jsonschema.validate(data, schema)
            success += 1
            print(f'✓ {f.name} valid')
        except jsonschema.ValidationError as e:
            errors.append(f'❌ {f.name}: {e.message}')
        except Exception as e:
            errors.append(f'❌ {f.name}: {str(e)}')

    if errors:
        print('\n'.join(errors))
        print(f'\n✗ Schema validation: {success}/{len(pilots)} pilots passed')
        return 1

    print(f'\n✓ Schema validation: {success}/{len(pilots)} pilots passed')
    return 0


def validate_all_chunks() -> int:
    """Validate all chunk files against schema."""
    schema = json.loads(Path('templates/chunk-constraints.schema.json').read_text())
    errors = []
    success = 0
    total = 0

    for f in sorted(Path('true-dual-tract/chunks').glob('chunk-*.constraints.json')):
        total += 1
        try:
            data = json.loads(f.read_text())
            jsonschema.validate(data, schema)
            success += 1
        except jsonschema.ValidationError as e:
            errors.append(f'❌ {f.name}: {e.message}')
        except Exception as e:
            errors.append(f'❌ {f.name}: {str(e)}')

    if errors:
        print('\n'.join(errors))
        print(f'\n✗ Schema validation: {success}/{total} chunks passed')
        return 1

    print(f'✓ Schema validation: {success}/{total} chunks passed')
    return 0


def main():
    """Main entry point for CI."""
    import argparse
    parser = argparse.ArgumentParser(description='Validate JSON constraint files against schema')
    parser.add_argument(
        '--pilots',
        nargs='+',
        help='Validate specific pilot chunks (e.g., 06 08 09 19)'
    )

    args = parser.parse_args()

    if args.pilots:
        return validate_pilot_chunks(args.pilots)
    else:
        return validate_all_chunks()


if __name__ == '__main__':
    sys.exit(main())