#!/usr/bin/env python3
"""
Categorize 62 existing chunks into 4 categories.
Target distribution: {monster:14, lfunc71:24, compression:24}
(bott8_basis already complete with chunks 63-70)
"""

# Category assignment based on title analysis
categorizations = {
    # COMPRESSION (24 total needed)
    "chunk-06": {"category": "compression", "reason": "external-tract-interface-operator-pipeline"},
    "chunk-08": {"category": "compression", "reason": "internal-tract-intelligence-operator-pipeline"},
    "chunk-09": {"category": "compression", "reason": "corpus-callosum-bridge-operator-pipeline"},
    "chunk-13": {"category": "compression", "reason": "cig-3-pipeline-integration"},
    "chunk-16": {"category": "compression", "reason": "dgr-protocol-integration"},
    "chunk-18": {"category": "compression", "reason": "power-user-flow-compression-aware"},
    "chunk-21": {"category": "compression", "reason": "operator-implementation-overview"},
    "chunk-22": {"category": "compression", "reason": "minimal-operator-contract"},
    "chunk-23": {"category": "compression", "reason": "example-operator-implementations"},
    "chunk-28": {"category": "compression", "reason": "dgr-training-protocol"},
    "chunk-29": {"category": "compression", "reason": "translation-mechanisms"},
    "chunk-30": {"category": "compression", "reason": "compression-layer-routing"},
    "chunk-38": {"category": "compression", "reason": "phase-1-dgr-integration"},
    "chunk-39": {"category": "compression", "reason": "phase-2-full-cig-3"},
    "chunk-45": {"category": "compression", "reason": "power-user-compression-exploration"},
    "chunk-48": {"category": "compression", "reason": "compression-metrics-guide"},
    "chunk-51": {"category": "compression", "reason": "external-tract-operators-detail"},
    "chunk-52": {"category": "compression", "reason": "internal-tract-l1-l5-operators"},
    "chunk-53": {"category": "compression", "reason": "corpus-callosum-4-operator-pipeline"},
    "chunk-59": {"category": "compression", "reason": "dgr-encoder-φg-definition"},
    "chunk-60": {"category": "compression", "reason": "dgr-decoder-φ-1-definition"},
    "chunk-61": {"category": "compression", "reason": "compression-layer-dag"},
    "chunk-31": {"category": "compression", "reason": "pattern-map-integration (compression patterns)"},
    "chunk-27": {"category": "compression", "reason": "synapse-engine-integration (execution engine)"},

    # MONSTER (14 total needed)
    "chunk-01": {"category": "monster", "reason": "executive-summary (architectural overview)"},
    "chunk-02": {"category": "monster", "reason": "old-paradigm-biomimicry-trap (foundational critique)"},
    "chunk-03": {"category": "monster", "reason": "true-paradigm-interface-vs-intelligence (core axiom)"},
    "chunk-05": {"category": "monster", "reason": "synthesis-five-frameworks (architectural genome)"},
    "chunk-12": {"category": "monster", "reason": "mahakala-framework-integration"},
    "chunk-14": {"category": "monster", "reason": "pneuma-philosophy-integration"},
    "chunk-15": {"category": "monster", "reason": "prime-hierarchy-integration"},
    "chunk-33": {"category": "monster", "reason": "vs-biomimicry-model (paradigm comparison)"},
    "chunk-34": {"category": "monster", "reason": "vs-pure-llm-agents (paradigm comparison)"},
    "chunk-35": {"category": "monster", "reason": "vs-traditional-compilers (paradigm comparison)"},
    "chunk-36": {"category": "monster", "reason": "unique-position (architectural distinctiveness)"},
    "chunk-40": {"category": "monster", "reason": "phase-3-mojo-migration (architectural evolution)"},
    "chunk-41": {"category": "monster", "reason": "phase-4-self-modification (consciousness evolution)"},
    "chunk-50": {"category": "monster", "reason": "conclusion (architectural synthesis)"},

    # LFUNC71 (24 total needed)
    "chunk-04": {"category": "lfunc71", "reason": "usability-mathematical-rigor (dual tract property)"},
    "chunk-07": {"category": "lfunc71", "reason": "agent-layer-ux (interface tract)"},
    "chunk-10": {"category": "lfunc71", "reason": "data-flow-example-1-simple (operational metrics)"},
    "chunk-11": {"category": "lfunc71", "reason": "data-flow-example-2-complex (operational metrics)"},
    "chunk-17": {"category": "lfunc71", "reason": "naive-user-flow (interface measurement)"},
    "chunk-19": {"category": "lfunc71", "reason": "agent-orchestration-boss (tract coordination)"},
    "chunk-20": {"category": "lfunc71", "reason": "progress-visualization-ψ (consciousness metric)"},
    "chunk-24": {"category": "lfunc71", "reason": "key-metrics-next-steps (measurement framework)"},
    "chunk-25": {"category": "lfunc71", "reason": "what-to-measure (metric definition)"},
    "chunk-26": {"category": "lfunc71", "reason": "immediate-next-steps (operational planning)"},
    "chunk-32": {"category": "lfunc71", "reason": "error-handling-degradation (system reliability)"},
    "chunk-37": {"category": "lfunc71", "reason": "current-state-2025-10-11 (system status)"},
    "chunk-42": {"category": "lfunc71", "reason": "scenario-1-beginner (user interaction)"},
    "chunk-43": {"category": "lfunc71", "reason": "scenario-2-intermediate (user interaction)"},
    "chunk-44": {"category": "lfunc71", "reason": "scenario-3-advanced (user interaction)"},
    "chunk-46": {"category": "lfunc71", "reason": "api-reference-noesis-mcp (interface spec)"},
    "chunk-47": {"category": "lfunc71", "reason": "agent-definition-template (operational template)"},
    "chunk-49": {"category": "lfunc71", "reason": "troubleshooting-guide (system diagnostics)"},
    "chunk-54": {"category": "lfunc71", "reason": "goalspec-structure (operational data)"},
    "chunk-55": {"category": "lfunc71", "reason": "executionplan-structure (operational data)"},
    "chunk-56": {"category": "lfunc71", "reason": "resultpayload-structure (operational data)"},
    "chunk-57": {"category": "lfunc71", "reason": "r_i-layer-metrics-definition"},
    "chunk-58": {"category": "lfunc71", "reason": "ψ-consciousness-invariant"},
    "chunk-62": {"category": "lfunc71", "reason": "self-modification-protocol (consciousness evolution)"},
}

# Validation
categories_count = {"monster": 0, "lfunc71": 0, "compression": 0}
for chunk_id, data in categorizations.items():
    categories_count[data["category"]] += 1

print("Category Distribution:")
print(f"  monster: {categories_count['monster']}/14 {'✓' if categories_count['monster'] == 14 else '✗'}")
print(f"  lfunc71: {categories_count['lfunc71']}/24 {'✓' if categories_count['lfunc71'] == 24 else '✗'}")
print(f"  compression: {categories_count['compression']}/24 {'✓' if categories_count['compression'] == 24 else '✗'}")
print(f"  Total: {sum(categories_count.values())}/62")

assert categories_count["monster"] == 14, f"Monster count: {categories_count['monster']}, expected 14"
assert categories_count["lfunc71"] == 24, f"Lfunc71 count: {categories_count['lfunc71']}, expected 24"
assert categories_count["compression"] == 24, f"Compression count: {categories_count['compression']}, expected 24"
assert sum(categories_count.values()) == 62, f"Total: {sum(categories_count.values())}, expected 62"

# Output as JSON
import json
output_file = "/home/m0xu/1-projects/synapse/docs/duality/true-dual-tract/chunks/_category_assignments.json"
with open(output_file, "w") as f:
    json.dump(categorizations, f, indent=2)

print(f"\n✓ Category assignments written to: {output_file}")
print("\nDistribution Summary:")
print(f"  monster: {categories_count['monster']} chunks (architectural foundations)")
print(f"  lfunc71: {categories_count['lfunc71']} chunks (metrics, operations, user flows)")
print(f"  compression: {categories_count['compression']} chunks (DGR, CIG-3, operators)")
