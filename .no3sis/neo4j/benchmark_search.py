#!/usr/bin/env python3
"""
Search Performance Benchmark
============================

Quick benchmark to test search improvements against a set of common queries.
"""

import sys
import time
import json
from pathlib import Path
from context_manager import SynapseContextManager

def load_test_queries(queries_file: Path = None) -> list:
    """Load test queries from file or use defaults"""
    default_queries = [
        "rust error handling",
        "python async function",
        "typescript interface",
        "golang concurrency",
        "test coverage",
        "authentication system",
        "database connection",
        "configuration management",
        "logging implementation",
        "file processing",
        "api endpoint",
        "dependency injection",
        "error recovery",
        "performance optimization",
        "security vulnerability",
        "debugging tools",
        "async await pattern",
        "test automation",
        "code review",
        "deployment script"
    ]

    if queries_file and queries_file.exists():
        try:
            with open(queries_file, 'r') as f:
                return [line.strip() for line in f if line.strip()]
        except Exception as e:
            print(f"Failed to load queries from {queries_file}: {e}")
            return default_queries

    return default_queries

def run_benchmark(queries: list, max_results: int = 5) -> dict:
    """Run search benchmark and collect metrics"""
    context_manager = SynapseContextManager()

    results = {
        "total_queries": len(queries),
        "successful_searches": 0,
        "failed_searches": 0,
        "cache_hits": 0,
        "vector_matches": 0,
        "graph_matches": 0,
        "fuzzy_matches": 0,
        "total_time": 0,
        "total_results": 0,
        "intent_distribution": {},
        "query_details": []
    }

    print(f"🔍 Running benchmark with {len(queries)} queries...")

    for i, query in enumerate(queries, 1):
        print(f"[{i:2d}/{len(queries)}] Testing: '{query[:40]}{'...' if len(query) > 40 else ''}'")

        try:
            start_time = time.time()
            result = context_manager.intelligent_search(query, max_results=max_results)
            search_time = time.time() - start_time

            # Collect metrics
            results["total_time"] += search_time

            if "error" not in result:
                results["successful_searches"] += 1

                # Count results
                nodes_found = result.get("nodes_found", 0)
                results["total_results"] += nodes_found

                # Track source
                source = result.get("source", "unknown")
                if source == "cache":
                    results["cache_hits"] += 1

                # Track intent
                intent = result.get("intent", "general")
                results["intent_distribution"][intent] = results["intent_distribution"].get(intent, 0) + 1

                # Track match types
                context = result.get("context", {})
                strategy = context.get("search_strategy", {})

                for match_type, count in strategy.items():
                    if "vector" in match_type:
                        results["vector_matches"] += count
                    elif "graph" in match_type or "general" in match_type:
                        results["graph_matches"] += count
                    elif "fuzzy" in match_type:
                        results["fuzzy_matches"] += count

                # Store detailed results
                results["query_details"].append({
                    "query": query,
                    "time": round(search_time, 3),
                    "results": nodes_found,
                    "source": source,
                    "intent": intent,
                    "strategy": strategy
                })

            else:
                results["failed_searches"] += 1
                print(f"  ❌ Search failed: {result.get('error')}")

        except Exception as e:
            results["failed_searches"] += 1
            print(f"  ❌ Exception: {e}")

    return results

def analyze_results(results: dict):
    """Analyze and display benchmark results"""
    print("\n" + "="*60)
    print("📊 BENCHMARK RESULTS")
    print("="*60)

    # Success rate
    success_rate = (results["successful_searches"] / results["total_queries"]) * 100
    print(f"✅ Success rate: {success_rate:.1f}% ({results['successful_searches']}/{results['total_queries']})")

    # Performance metrics
    avg_time = results["total_time"] / results["total_queries"]
    avg_results = results["total_results"] / max(results["successful_searches"], 1)

    print(f"⏱️  Average search time: {avg_time:.3f}s")
    print(f"📁 Average results per query: {avg_results:.1f}")
    print(f"💾 Cache hit rate: {(results['cache_hits'] / results['total_queries']) * 100:.1f}%")

    # Match type distribution
    total_matches = results["vector_matches"] + results["graph_matches"] + results["fuzzy_matches"]
    if total_matches > 0:
        print(f"\n🎯 Match type distribution:")
        print(f"   Vector: {(results['vector_matches'] / total_matches) * 100:.1f}%")
        print(f"   Graph: {(results['graph_matches'] / total_matches) * 100:.1f}%")
        print(f"   Fuzzy: {(results['fuzzy_matches'] / total_matches) * 100:.1f}%")

    # Intent distribution
    print(f"\n🧠 Intent classification:")
    for intent, count in sorted(results["intent_distribution"].items()):
        percentage = (count / results["successful_searches"]) * 100
        print(f"   {intent}: {percentage:.1f}% ({count})")

    # Performance highlights
    fastest_queries = sorted(results["query_details"], key=lambda x: x["time"])[:3]
    slowest_queries = sorted(results["query_details"], key=lambda x: x["time"], reverse=True)[:3]

    print(f"\n⚡ Fastest queries:")
    for i, query_result in enumerate(fastest_queries, 1):
        print(f"   {i}. '{query_result['query'][:30]}...' - {query_result['time']}s")

    print(f"\n🐌 Slowest queries:")
    for i, query_result in enumerate(slowest_queries, 1):
        print(f"   {i}. '{query_result['query'][:30]}...' - {query_result['time']}s")

def save_results(results: dict, output_file: Path):
    """Save detailed results to JSON file"""
    try:
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n💾 Detailed results saved to: {output_file}")
    except Exception as e:
        print(f"\n❌ Failed to save results: {e}")

def main():
    """Main benchmark function"""
    # Parse command line arguments
    queries_file = None
    output_file = Path("benchmark_results.json")

    if len(sys.argv) > 1:
        queries_file = Path(sys.argv[1])

    if len(sys.argv) > 2:
        output_file = Path(sys.argv[2])

    # Load queries and run benchmark
    queries = load_test_queries(queries_file)

    print("🚀 Enhanced Search Benchmark")
    print(f"📝 Testing {len(queries)} queries")
    if queries_file:
        print(f"📁 Queries from: {queries_file}")
    print("-" * 50)

    # Run the benchmark
    results = run_benchmark(queries)

    # Analyze and display results
    analyze_results(results)

    # Save detailed results
    save_results(results, output_file)

    print(f"\n🏁 Benchmark completed!")

if __name__ == "__main__":
    main()