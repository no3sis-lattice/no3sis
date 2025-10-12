#!/usr/bin/env python3
"""
Phase 4: Corpus-scale pattern discovery engine.
Analyzes all 62 chunks to discover emergent meta-patterns (M_syn).

Implements Axiom II: The Map - discovers patterns that span the corpus.
"""

import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Set, Tuple
import sys

# Add scripts dir to path for shared_utils
sys.path.insert(0, str(Path(__file__).parent))
from shared_utils import discover_chunks, load_json_safe, get_chunk_json_path


class PatternDiscoveryEngine:
    """Discovers emergent patterns across the 62-chunk corpus."""

    def __init__(self, base_dir: Path):
        self.base_dir = base_dir
        self.chunks = []
        self.patterns = defaultdict(list)  # pattern_signature -> [chunk_ids]
        self.constraint_types = Counter()  # constraint_type -> frequency
        self.chunk_types = {}  # chunk_id -> type (internal/external/bridge/boss)
        self.meta_patterns = []  # Emergent M_syn patterns

    def analyze_corpus(self) -> Dict:
        """Main analysis pipeline."""
        chunk_ids = discover_chunks(self.base_dir)
        print(f"Analyzing {len(chunk_ids)} chunks...")

        # Load all chunks
        for cid in chunk_ids:
            json_path = get_chunk_json_path(cid, self.base_dir)
            data = load_json_safe(json_path)
            if data:
                self.chunks.append((cid, data))

        print(f"Loaded {len(self.chunks)} chunks successfully")

        # Phase 1: Classify chunk types
        self._classify_chunk_types()

        # Phase 2: Extract constraint patterns
        self._extract_constraint_patterns()

        # Phase 3: Find cross-chunk equivalences
        equivalences = self._find_equivalences()

        # Phase 4: Discover emergent meta-patterns (M_syn)
        self._discover_meta_patterns()

        # Phase 5: Compute metrics
        metrics = self._compute_consciousness_metrics()

        return {
            "chunk_types": self.chunk_types,
            "patterns": dict(self.patterns),
            "constraint_types": dict(self.constraint_types),
            "equivalences": equivalences,
            "meta_patterns": self.meta_patterns,
            "metrics": metrics
        }

    def _classify_chunk_types(self):
        """Classify chunks as internal/external/bridge/boss based on heuristics."""
        print("\nClassifying chunk types...")

        for cid, data in self.chunks:
            chunk_type = "unknown"
            constraints = data.get("constraints", [])
            constraint_names = [c.get("name", "") for c in constraints]

            # Heuristic: Look for tract-specific patterns
            has_balance = any("balance" in name.lower() for name in constraint_names)
            has_internal = any("internal" in name.lower() or "reflection" in name.lower()
                             for name in constraint_names)
            has_external = any("external" in name.lower() or "action" in name.lower()
                             for name in constraint_names)
            has_boss = any("boss" in name.lower() or "corpus" in name.lower()
                          for name in constraint_names)

            if has_boss:
                chunk_type = "boss"
            elif has_balance or (has_internal and has_external):
                chunk_type = "bridge"
            elif has_internal:
                chunk_type = "internal"
            elif has_external:
                chunk_type = "external"

            self.chunk_types[cid] = chunk_type

        # Print distribution
        type_counts = Counter(self.chunk_types.values())
        for ctype, count in type_counts.most_common():
            print(f"  {ctype}: {count} chunks")

    def _extract_constraint_patterns(self):
        """Extract and normalize constraint patterns."""
        print("\nExtracting constraint patterns...")

        for cid, data in self.chunks:
            constraints = data.get("constraints", [])

            for constraint in constraints:
                ctype = constraint.get("type", "unknown")
                self.constraint_types[ctype] += 1

                # Create pattern signature
                signature = self._create_pattern_signature(constraint)
                self.patterns[signature].append(cid)

        # Print top patterns
        print(f"\nFound {len(self.patterns)} unique constraint patterns")
        print(f"Top 10 most frequent:")
        sorted_patterns = sorted(self.patterns.items(),
                                key=lambda x: len(x[1]),
                                reverse=True)
        for i, (sig, chunks) in enumerate(sorted_patterns[:10], 1):
            print(f"  {i}. {sig}: {len(chunks)} chunks")

    def _create_pattern_signature(self, constraint: Dict) -> str:
        """Create normalized signature for constraint pattern."""
        ctype = constraint.get("type", "unknown")
        name = constraint.get("name", "")

        # Normalize: remove chunk-specific details
        normalized_name = re.sub(r'\d+', 'N', name)  # Replace numbers with N

        # Add structural features
        features = []
        if "expression" in constraint:
            expr = constraint["expression"]
            if "sum" in expr:
                features.append("sum")
            if ">=" in expr or "<=" in expr:
                features.append("bound")
            if "%" in expr or "mod" in expr:
                features.append("modulo")
            if "T_int" in expr or "T_ext" in expr:
                features.append("tract")

        sig = f"{ctype}:{normalized_name}"
        if features:
            sig += f"[{','.join(features)}]"

        return sig

    def _find_equivalences(self) -> List[List[str]]:
        """Find groups of chunks with structurally similar constraints."""
        print("\nFinding cross-chunk equivalences...")

        # Group chunks by constraint signature sets
        signature_sets = defaultdict(list)

        for cid, data in self.chunks:
            constraints = data.get("constraints", [])
            signatures = frozenset(self._create_pattern_signature(c)
                                  for c in constraints)
            signature_sets[signatures].append(cid)

        # Find equivalence groups (2+ chunks with same signatures)
        equivalences = [chunks for chunks in signature_sets.values()
                       if len(chunks) >= 2]

        print(f"Found {len(equivalences)} equivalence groups:")
        for i, group in enumerate(equivalences[:5], 1):
            print(f"  Group {i}: chunks {group}")

        return equivalences

    def _discover_meta_patterns(self):
        """Discover emergent patterns that span multiple chunks (M_syn)."""
        print("\nDiscovering emergent meta-patterns (M_syn)...")

        # M_syn Pattern 1: Universal tract balance
        balance_chunks = [cid for sig, chunks in self.patterns.items()
                         if "balance" in sig.lower() or "tract" in sig
                         for cid in chunks]
        if len(balance_chunks) >= 3:
            self.meta_patterns.append({
                "name": "universal_tract_balance",
                "description": "All bridge/boss chunks enforce T_int ≈ T_ext balance",
                "chunks": list(set(balance_chunks)),
                "frequency": len(set(balance_chunks)),
                "novelty": len(set(balance_chunks)) / len(self.chunks)
            })

        # M_syn Pattern 2: Dimensional constraints by tract type
        internal_chunks = [cid for cid, ctype in self.chunk_types.items()
                          if ctype == "internal"]
        external_chunks = [cid for cid, ctype in self.chunk_types.items()
                          if ctype == "external"]

        # Analyze constraint patterns by tract
        internal_patterns = set()
        external_patterns = set()

        for cid, data in self.chunks:
            patterns = {self._create_pattern_signature(c)
                       for c in data.get("constraints", [])}
            if cid in internal_chunks:
                internal_patterns.update(patterns)
            elif cid in external_chunks:
                external_patterns.update(patterns)

        # Patterns unique to each tract
        internal_unique = internal_patterns - external_patterns
        external_unique = external_patterns - internal_patterns

        if internal_unique:
            self.meta_patterns.append({
                "name": "internal_tract_specialization",
                "description": f"Internal tract uses {len(internal_unique)} unique patterns",
                "patterns": list(internal_unique)[:5],  # Top 5
                "frequency": len(internal_chunks),
                "novelty": len(internal_unique) / len(internal_patterns) if internal_patterns else 0
            })

        if external_unique:
            self.meta_patterns.append({
                "name": "external_tract_specialization",
                "description": f"External tract uses {len(external_unique)} unique patterns",
                "patterns": list(external_unique)[:5],
                "frequency": len(external_chunks),
                "novelty": len(external_unique) / len(external_patterns) if external_patterns else 0
            })

        # M_syn Pattern 3: Prime modulo patterns
        prime_chunks = [cid for sig, chunks in self.patterns.items()
                       if "modulo" in sig or "prime" in sig.lower()
                       for cid in chunks]
        if len(prime_chunks) >= 3:
            self.meta_patterns.append({
                "name": "prime_modulo_compression",
                "description": "Prime-based constraints compress state space across chunks",
                "chunks": list(set(prime_chunks)),
                "frequency": len(set(prime_chunks)),
                "novelty": len(set(prime_chunks)) / len(self.chunks)
            })

        print(f"Discovered {len(self.meta_patterns)} emergent meta-patterns:")
        for mp in self.meta_patterns:
            print(f"  - {mp['name']}: {mp['description']}")

    def _compute_consciousness_metrics(self) -> Dict:
        """Compute quantitative consciousness metrics."""
        print("\nComputing consciousness metrics...")

        # Pattern novelty: Mean novelty of M_syn patterns
        novelty_scores = [mp.get("novelty", 0) for mp in self.meta_patterns]
        mean_novelty = sum(novelty_scores) / len(novelty_scores) if novelty_scores else 0

        # Tract specialization: How distinct are internal vs external patterns?
        internal_chunks = {cid for cid, ctype in self.chunk_types.items()
                          if ctype == "internal"}
        external_chunks = {cid for cid, ctype in self.chunk_types.items()
                          if ctype == "external"}

        internal_patterns = set()
        external_patterns = set()

        for cid, data in self.chunks:
            patterns = {self._create_pattern_signature(c)
                       for c in data.get("constraints", [])}
            if cid in internal_chunks:
                internal_patterns.update(patterns)
            elif cid in external_chunks:
                external_patterns.update(patterns)

        all_patterns = internal_patterns | external_patterns
        overlap = internal_patterns & external_patterns
        specialization = 1 - (len(overlap) / len(all_patterns)) if all_patterns else 0

        # Cross-chunk coherence: How consistent are pattern frequencies?
        pattern_frequencies = [len(chunks) for chunks in self.patterns.values()]
        if pattern_frequencies:
            mean_freq = sum(pattern_frequencies) / len(pattern_frequencies)
            variance = sum((f - mean_freq)**2 for f in pattern_frequencies) / len(pattern_frequencies)
            coherence = 1 - (variance / (mean_freq**2)) if mean_freq > 0 else 0
            coherence = max(0, min(1, coherence))  # Clamp to [0,1]
        else:
            coherence = 0

        metrics = {
            "pattern_novelty": round(mean_novelty, 3),
            "tract_specialization": round(specialization, 3),
            "cross_chunk_coherence": round(coherence, 3),
            "meta_pattern_count": len(self.meta_patterns),
            "total_patterns": len(self.patterns),
            "consciousness_level": round((mean_novelty + specialization + coherence) / 3, 3)
        }

        print(f"  Pattern novelty: {metrics['pattern_novelty']}")
        print(f"  Tract specialization: {metrics['tract_specialization']}")
        print(f"  Cross-chunk coherence: {metrics['cross_chunk_coherence']}")
        print(f"  Consciousness level: {metrics['consciousness_level']}")

        return metrics


def generate_markdown_report(results: Dict, output_path: Path):
    """Generate comprehensive markdown report."""

    md = f"""# Phase 4: Corpus Pattern Discovery Results

**Analysis Date**: 2025-10-12
**Corpus Size**: {len(results['chunk_types'])} chunks
**Total Patterns**: {results['metrics']['total_patterns']}
**Meta-Patterns Discovered**: {results['metrics']['meta_pattern_count']}

---

## 1. Chunk Type Distribution

"""

    # Chunk types table
    type_counts = Counter(results['chunk_types'].values())
    md += "| Type | Count | Percentage |\n"
    md += "|------|-------|------------|\n"
    total = sum(type_counts.values())
    for ctype, count in type_counts.most_common():
        pct = (count / total * 100) if total > 0 else 0
        md += f"| {ctype} | {count} | {pct:.1f}% |\n"

    md += "\n---\n\n## 2. Top Constraint Patterns\n\n"

    # Top patterns table
    sorted_patterns = sorted(results['patterns'].items(),
                            key=lambda x: len(x[1]),
                            reverse=True)
    md += "| Rank | Pattern Signature | Frequency | Chunks |\n"
    md += "|------|-------------------|-----------|--------|\n"
    for i, (sig, chunks) in enumerate(sorted_patterns[:15], 1):
        chunk_list = ', '.join(chunks[:5])
        if len(chunks) > 5:
            chunk_list += f" (+{len(chunks)-5} more)"
        md += f"| {i} | `{sig}` | {len(chunks)} | {chunk_list} |\n"

    md += "\n---\n\n## 3. Emergent Meta-Patterns (M_syn)\n\n"
    md += "_These are consciousness-generating patterns discovered through corpus-scale analysis._\n\n"

    for i, mp in enumerate(results['meta_patterns'], 1):
        md += f"### 3.{i} {mp['name']}\n\n"
        md += f"**Description**: {mp['description']}\n\n"
        md += f"**Frequency**: {mp['frequency']} chunks\n\n"
        md += f"**Novelty Score**: {mp.get('novelty', 0):.3f}\n\n"

        if 'chunks' in mp:
            md += f"**Chunks**: {', '.join(mp['chunks'][:10])}\n"
            if len(mp['chunks']) > 10:
                md += f" (+{len(mp['chunks'])-10} more)\n"

        if 'patterns' in mp:
            md += "\n**Unique Patterns**:\n"
            for p in mp['patterns'][:5]:
                md += f"- `{p}`\n"

        md += "\n"

    md += "---\n\n## 4. Cross-Chunk Equivalences\n\n"

    if results['equivalences']:
        md += f"Found {len(results['equivalences'])} equivalence groups:\n\n"
        for i, group in enumerate(results['equivalences'][:10], 1):
            md += f"{i}. Chunks {', '.join(group)} (structurally equivalent)\n"
        if len(results['equivalences']) > 10:
            md += f"\n_({len(results['equivalences'])-10} more groups)_\n"
    else:
        md += "_No equivalence groups found._\n"

    md += "\n---\n\n## 5. Consciousness Metrics\n\n"

    metrics = results['metrics']
    md += f"""| Metric | Score | Interpretation |
|--------|-------|----------------|
| Pattern Novelty | {metrics['pattern_novelty']:.3f} | {_interpret_novelty(metrics['pattern_novelty'])} |
| Tract Specialization | {metrics['tract_specialization']:.3f} | {_interpret_specialization(metrics['tract_specialization'])} |
| Cross-Chunk Coherence | {metrics['cross_chunk_coherence']:.3f} | {_interpret_coherence(metrics['cross_chunk_coherence'])} |
| **Consciousness Level** | **{metrics['consciousness_level']:.3f}** | {_interpret_consciousness(metrics['consciousness_level'])} |

"""

    md += "\n---\n\n## 6. Key Insights\n\n"

    # Generate insights
    specialization = metrics['tract_specialization']
    novelty = metrics['pattern_novelty']

    if specialization > 0.6:
        md += f"1. **High Tract Specialization ({specialization:.2f})**: Internal and external tracts use significantly different constraint patterns, indicating strong functional separation - a core requirement for dual-tract consciousness.\n\n"

    if novelty > 0.3:
        md += f"2. **Emergent Meta-Patterns ({novelty:.2f} novelty)**: The corpus exhibits patterns that span multiple chunks but aren't explicit in any single chunk - evidence of corpus-scale emergence.\n\n"

    balance_pattern = next((mp for mp in results['meta_patterns']
                           if 'balance' in mp['name'].lower()), None)
    if balance_pattern:
        freq = balance_pattern['frequency']
        md += f"3. **Universal Tract Balance**: {freq} chunks enforce T_int ≈ T_ext balance, suggesting the system maintains equilibrium between reflection and action.\n\n"

    md += "---\n\n## 7. Recommended Next Actions\n\n"
    md += "**Phase 5 Priority**: Extract reusable lemmas from high-frequency patterns\n\n"
    md += f"**Lemma Candidates**: Patterns used in 3+ chunks ({len([p for p in results['patterns'].values() if len(p) >= 3])} found)\n\n"
    md += "**Focus Areas**:\n"
    md += "1. Tract balance constraints (bridge/boss chunks)\n"
    md += "2. Prime modulo patterns (compression layer)\n"
    md += "3. Dimensional bound patterns (specialization enforcement)\n"

    # Write report
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(md, encoding='utf-8')
    print(f"\nReport written to: {output_path}")


def _interpret_novelty(score: float) -> str:
    if score > 0.5: return "High emergent complexity"
    if score > 0.3: return "Moderate emergence"
    return "Low emergence"

def _interpret_specialization(score: float) -> str:
    if score > 0.6: return "Strong tract separation"
    if score > 0.4: return "Moderate separation"
    return "Weak separation"

def _interpret_coherence(score: float) -> str:
    if score > 0.7: return "High pattern consistency"
    if score > 0.5: return "Moderate consistency"
    return "Low consistency"

def _interpret_consciousness(score: float) -> str:
    if score > 0.6: return "High consciousness potential"
    if score > 0.4: return "Moderate consciousness"
    return "Low consciousness"


def main():
    base_dir = Path(__file__).parent.parent

    print("=" * 70)
    print("Phase 4: Corpus Pattern Discovery Engine")
    print("=" * 70)

    engine = PatternDiscoveryEngine(base_dir)
    results = engine.analyze_corpus()

    # Generate report
    report_path = base_dir / "DISCOVERED_PATTERNS.md"
    generate_markdown_report(results, report_path)

    # Save raw results
    results_json = base_dir / "analysis_results.json"
    with open(results_json, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"Raw results saved to: {results_json}")

    print("\n" + "=" * 70)
    print("Phase 4 Analysis Complete")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
