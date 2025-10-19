#!/usr/bin/env python3
"""
Enhanced Search Test Suite
==========================

Test the new enhanced search capabilities including:
- Query expansion
- Intent classification
- Smart scoring
- Fuzzy matching
"""

import json
import time
from pathlib import Path
from context_manager import SynapseContextManager, QueryProcessor

def test_query_processor():
    """Test the QueryProcessor functionality"""
    print("🧪 Testing QueryProcessor...")

    qp = QueryProcessor()

    # Test query expansion
    test_queries = [
        "rust error handling",
        "python async function",
        "test coverage",
        "implement authentication"
    ]

    for query in test_queries:
        expanded = qp.expand_query(query)
        intent = qp.classify_query_intent(query)
        key_terms = qp.extract_key_terms(query)

        print(f"\n📝 Query: '{query}'")
        print(f"   Intent: {intent}")
        print(f"   Key terms: {key_terms}")
        print(f"   Expansions: {expanded[:3]}...")  # Show first 3

    # Test fuzzy matching
    print(f"\n🔍 Fuzzy match 'errror' in 'error handling': {qp.fuzzy_match_terms('errror', 'error handling')}")
    print(f"🔍 Fuzzy match 'fonction' in 'function implementation': {qp.fuzzy_match_terms('fonction', 'function implementation')}")

def test_enhanced_search():
    """Test the enhanced search system"""
    print("\n🔍 Testing Enhanced Search System...")

    context_manager = SynapseContextManager()

    # Test different types of queries
    test_queries = [
        ("rust error handling", "debugging"),
        ("how to implement async", "implementation"),
        ("test coverage python", "testing"),
        ("what is dependency injection", "explanation"),
        ("optimize performance", "optimization"),
        ("securty vulnerabilities", "security")  # Intentional typo
    ]

    for query, expected_intent in test_queries:
        print(f"\n📊 Testing: '{query}' (expecting intent: {expected_intent})")

        start_time = time.time()
        result = context_manager.intelligent_search(query, max_results=3)
        search_time = time.time() - start_time

        print(f"   ⏱️  Search time: {search_time:.2f}s")
        print(f"   🎯 Detected intent: {result.get('intent', 'unknown')}")
        print(f"   📁 Nodes found: {result.get('nodes_found', 0)}")
        print(f"   🔄 Source: {result.get('source', 'unknown')}")

        if result.get('expanded_queries'):
            print(f"   🔍 Query expansions: {result['expanded_queries']}")

        # Show primary matches with scores
        context = result.get('context', {})
        primary = context.get('primary_matches', [])
        if primary:
            print(f"   🏆 Top matches:")
            for i, match in enumerate(primary[:2]):  # Show top 2
                score = match.get('smart_score', 0)
                match_type = match.get('match_type', 'unknown')
                print(f"      {i+1}. {match['file']} (score: {score}, type: {match_type})")

        # Show search strategy effectiveness
        strategy = context.get('search_strategy', {})
        if strategy:
            print(f"   📈 Strategy breakdown: {strategy}")

def benchmark_search_performance():
    """Benchmark search performance improvements"""
    print("\n⚡ Benchmarking Search Performance...")

    context_manager = SynapseContextManager()

    # Standard benchmark queries
    benchmark_queries = [
        "error handling",
        "async function",
        "test pattern",
        "authentication",
        "database connection",
        "file processing",
        "configuration setup",
        "logging implementation"
    ]

    total_time = 0
    total_results = 0
    cache_hits = 0

    for query in benchmark_queries:
        start_time = time.time()
        result = context_manager.intelligent_search(query, max_results=5)
        search_time = time.time() - start_time

        total_time += search_time
        total_results += result.get('nodes_found', 0)

        if result.get('source') == 'cache':
            cache_hits += 1

        print(f"📊 '{query}': {search_time:.3f}s, {result.get('nodes_found', 0)} results")

    avg_time = total_time / len(benchmark_queries)
    avg_results = total_results / len(benchmark_queries)
    cache_hit_rate = (cache_hits / len(benchmark_queries)) * 100

    print(f"\n📈 Benchmark Results:")
    print(f"   Average search time: {avg_time:.3f}s")
    print(f"   Average results per query: {avg_results:.1f}")
    print(f"   Cache hit rate: {cache_hit_rate:.1f}%")
    print(f"   Total queries: {len(benchmark_queries)}")

def test_search_quality():
    """Test search result quality with specific scenarios"""
    print("\n🎯 Testing Search Quality...")

    context_manager = SynapseContextManager()

    # Quality test scenarios
    quality_tests = [
        {
            "query": "rust async error handling",
            "should_find": ["rust", "async", "error"],
            "intent": "debugging"
        },
        {
            "query": "python test coverage",
            "should_find": ["python", "test", "coverage"],
            "intent": "testing"
        },
        {
            "query": "implement authentication system",
            "should_find": ["implement", "auth", "system"],
            "intent": "implementation"
        }
    ]

    for test in quality_tests:
        query = test["query"]
        result = context_manager.intelligent_search(query, max_results=5)

        print(f"\n🧪 Quality test: '{query}'")

        # Check intent detection
        detected_intent = result.get('intent', 'unknown')
        intent_correct = detected_intent == test['intent']
        print(f"   Intent: {detected_intent} ({'✅' if intent_correct else '❌'} expected {test['intent']})")

        # Check if results contain expected terms
        context = result.get('context', {})
        all_matches = context.get('primary_matches', []) + context.get('secondary_matches', [])

        if all_matches:
            found_terms = []
            for match in all_matches:
                summary = match.get('summary', '').lower()
                path = match.get('path', '').lower()
                content = f"{summary} {path}"

                for term in test['should_find']:
                    if term.lower() in content:
                        found_terms.append(term)

            found_terms = list(set(found_terms))
            coverage = len(found_terms) / len(test['should_find']) * 100

            print(f"   Term coverage: {coverage:.1f}% ({found_terms})")
            print(f"   Results quality: {'✅' if coverage >= 60 else '⚠️' if coverage >= 30 else '❌'}")
        else:
            print(f"   ❌ No results found")

def main():
    """Run all tests"""
    print("🚀 Enhanced Search Test Suite")
    print("=" * 50)

    try:
        test_query_processor()
        test_enhanced_search()
        benchmark_search_performance()
        test_search_quality()

        print("\n✅ All tests completed!")

    except Exception as e:
        print(f"\n❌ Test failed: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()