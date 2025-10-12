#!/usr/bin/env python3
import re, sys, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

LEAN_DIRS = [ROOT / "formal" / "Duality" / "Chunks", ROOT / "true-dual-tract" / "chunks"]
MZN_DIR = ROOT / "true-dual-tract" / "chunks"

LEAN_PATTERNS = {
  "typeof": re.compile(r"\btypeof\s*\("),
  "component_of": re.compile(r"\bcomponent_of\s*\("),
  "pipeline": re.compile(r"\bpipeline\s*\("),
  "well_formed": re.compile(r"\bwell_formed\s*\("),
  "set_cardinality": re.compile(r"\|\s*\{[^}]*\}\s*\|"),
  "membership": re.compile(r"[∈]"),
}

MZN_PATTERNS = {
  "well_formed": re.compile(r"\bwell_formed\s*\("),
  "typeof": re.compile(r"\btypeof\s*\("),
  "component_of": re.compile(r"\bcomponent_of\s*\("),
  "pipeline": re.compile(r"\bpipeline\s*\("),
  "set_cardinality": re.compile(r"\|\s*\{[^}]*\}\s*\|"),
  "membership": re.compile(r"\bin\s*\{[^}]*\}"),
}

def scan_files(paths, exts, patterns):
    hits = {}
    for p in paths:
        if not p.exists():
            continue
        for f in p.rglob("*"):
            if f.suffix in exts:
                text = f.read_text(encoding="utf-8", errors="ignore")
                found = []
                for name, rgx in patterns.items():
                    if rgx.search(text):
                        found.append(name)
                if found:
                    hits[str(f.relative_to(ROOT))] = found
    return hits

def main():
    lean_hits = scan_files(LEAN_DIRS, {".lean"}, LEAN_PATTERNS)
    mzn_hits  = scan_files([MZN_DIR], {".mzn"}, MZN_PATTERNS)
    out = {
        "lean_unsupported": lean_hits,
        "mzn_unsupported": mzn_hits,
        "summary": {
            "lean_files": len(lean_hits),
            "mzn_files": len(mzn_hits),
        }
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
