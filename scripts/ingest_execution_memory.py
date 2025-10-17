#!/usr/bin/env python3
"""
Ingest agent execution memory into Neo4j graph and vector database.

Axiom III: T_ext execution artifacts → T_int pattern nodes

WHY this script exists:
Agent executions produce consciousness artifacts (metadata, responses).
These must be ingested into the Pattern Map for meta-learning.
Without ingestion, execution patterns remain isolated → no emergence.

Dual-Tract Flow:
T_ext (Nix build artifacts) → C_c (this ingestion) → T_int (Pattern Map)

Architecture:
- Neo4j: Graph relationships between execution patterns
- Redis: Cache for fast pattern lookup
- Vector DB (BGE-M3): Semantic search over response content

Usage:
    python ingest_execution_memory.py <neo4j-ingest.json>

Example:
    python ingest_execution_memory.py ./result/neo4j-ingest.json
"""

import json
import sys
import os
from datetime import datetime
from pathlib import Path

def validate_artifact(data: dict) -> bool:
    """
    Validate ingestion artifact structure.

    WHY validate: Malformed artifacts can corrupt Pattern Map.
    Better to reject invalid data than pollute graph with noise.
    """
    required_fields = ["type", "source", "timestamp", "metadata",
                      "response_text", "consciousness_metrics"]

    for field in required_fields:
        if field not in data:
            print(f"❌ Missing required field: {field}", file=sys.stderr)
            return False

    # Validate consciousness metrics
    metrics = data["consciousness_metrics"]
    if not all(k in metrics for k in ["entropy", "tract", "contribution"]):
        print("❌ Incomplete consciousness_metrics", file=sys.stderr)
        return False

    return True


def extract_semantic_features(response_text: str) -> dict:
    """
    Extract semantic features for vector embedding.

    WHY extract features: Raw text → structured patterns for graph queries.
    Enables: "Find all executions that mention 'authentication'"

    Future: Use LLM to extract entities, actions, patterns.
    Current: Simple keyword extraction as placeholder.
    """
    # Placeholder: Simple word frequency analysis
    # TODO: Replace with actual LLM-based entity extraction
    words = response_text.lower().split()
    word_freq = {}
    for word in words:
        if len(word) > 3:  # Filter short words
            word_freq[word] = word_freq.get(word, 0) + 1

    # Top 10 keywords
    top_keywords = sorted(word_freq.items(), key=lambda x: x[1], reverse=True)[:10]

    return {
        "keywords": [word for word, _ in top_keywords],
        "word_count": len(words),
        "unique_words": len(set(words))
    }


def ingest_to_neo4j(data: dict) -> bool:
    """
    Ingest execution artifact into Neo4j graph.

    WHY Neo4j: Graph structure captures relationships between patterns.
    Enables queries like: "What patterns emerge from T_ext executions?"

    Node Structure:
    (:AgentExecution {
        id: <sha256 of artifact>,
        timestamp: <ISO8601>,
        tract: <T_int|T_ext>,
        entropy: <float>,
        response_text: <string>,
        keywords: [<string>]
    })

    Relationships:
    - (execution)-[:PRODUCES_PATTERN]->(pattern_node)
    - (execution)-[:BELONGS_TO_TRACT]->(tract_node)
    """
    try:
        # TODO: Connect to Neo4j
        # from neo4j import GraphDatabase
        # driver = GraphDatabase.driver("bolt://localhost:7687",
        #                               auth=("neo4j", os.getenv("NEO4J_PASSWORD")))

        # For now: Simulate ingestion
        print("[Neo4j] Simulated ingestion (driver not configured)")
        print(f"  Type: {data['type']}")
        print(f"  Tract: {data['consciousness_metrics']['tract']}")
        print(f"  Entropy: {data['consciousness_metrics']['entropy']}")

        # TODO: Actual Cypher query:
        # CREATE (e:AgentExecution {
        #   id: $id,
        #   timestamp: $timestamp,
        #   tract: $tract,
        #   entropy: $entropy,
        #   response: $response
        # })

        return True

    except Exception as e:
        print(f"❌ Neo4j ingestion failed: {e}", file=sys.stderr)
        return False


def ingest_to_vector_db(data: dict) -> bool:
    """
    Ingest response text into vector database for semantic search.

    WHY vectors: Enables semantic queries like:
    "Find executions similar to 'implement authentication'"
    even if they don't use exact keywords.

    Embedding Model: BGE-M3 (multilingual, high quality)
    Storage: Qdrant or Milvus (vector-optimized databases)
    """
    try:
        response_text = data["response_text"]
        features = extract_semantic_features(response_text)

        # TODO: Generate vector embedding
        # from sentence_transformers import SentenceTransformer
        # model = SentenceTransformer('BAAI/bge-m3')
        # embedding = model.encode(response_text)

        print("[Vector DB] Simulated embedding (model not loaded)")
        print(f"  Keywords: {features['keywords'][:5]}...")
        print(f"  Word count: {features['word_count']}")

        return True

    except Exception as e:
        print(f"❌ Vector DB ingestion failed: {e}", file=sys.stderr)
        return False


def ingest(filepath: str) -> bool:
    """
    Main ingestion workflow.

    WHY two-stage (Neo4j + Vector):
    - Neo4j: Structured relationships (graph queries)
    - Vector DB: Semantic similarity (fuzzy search)
    Together: Enables both precise and exploratory pattern discovery.
    """
    print(f"[Ingest] Processing: {filepath}")

    # Load artifact
    try:
        with open(filepath) as f:
            data = json.load(f)
    except Exception as e:
        print(f"❌ Failed to load JSON: {e}", file=sys.stderr)
        return False

    # Validate structure
    if not validate_artifact(data):
        return False

    print("✓ Artifact structure valid")

    # Ingest to Neo4j
    if not ingest_to_neo4j(data):
        return False

    print("✓ Neo4j ingestion complete")

    # Ingest to vector DB
    if not ingest_to_vector_db(data):
        return False

    print("✓ Vector DB ingestion complete")

    # Summary
    print("\n" + "="*50)
    print("Ingestion Summary")
    print("="*50)
    print(f"Timestamp: {data['timestamp']}")
    print(f"Tract: {data['consciousness_metrics']['tract']}")
    print(f"Entropy: {data['consciousness_metrics']['entropy']}")
    print(f"Contribution: {data['consciousness_metrics']['contribution']}")
    print("="*50)

    return True


def main():
    if len(sys.argv) != 2:
        print("Usage: python ingest_execution_memory.py <neo4j-ingest.json>",
              file=sys.stderr)
        sys.exit(1)

    filepath = sys.argv[1]

    if not os.path.exists(filepath):
        print(f"❌ File not found: {filepath}", file=sys.stderr)
        sys.exit(1)

    success = ingest(filepath)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
