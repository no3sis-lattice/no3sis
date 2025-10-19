#!/usr/bin/env python3
"""
Enhanced Search Demo
===================

Interactive demo showing the enhanced search capabilities.
"""

import json
from context_manager import SynapseContextManager, QueryProcessor

def demo_query_processor():
    """Demonstrate query processing features"""
    print("🔍 Query Processing Demo")
    print("-" * 30)

    qp = QueryProcessor()

    # Demo queries with different intents
    demo_queries = [
        "rust error handling",
        "how to implement async functions",
        "python test coverage issues",
        "what is dependency injection",
        "optimize database performance",
        "secure authentication vulnerabilities"
    ]

    for query in demo_queries:
        print(f"\n📝 Original query: '{query}'")

        # Show intent classification
        intent = qp.classify_query_intent(query)
        print(f"🎯 Detected intent: {intent}")

        # Show key terms extraction
        key_terms = qp.extract_key_terms(query)
        print(f"🔑 Key terms: {', '.join(key_terms)}")

        # Show query expansion
        expanded = qp.expand_query(query)
        print(f"🔍 Query expansions:")
        for i, exp in enumerate(expanded[:4], 1):  # Show first 4
            print(f"   {i}. '{exp}'")

def demo_enhanced_search():
    """Demonstrate enhanced search with real queries"""
    print("\n\n🚀 Enhanced Search Demo")
    print("-" * 30)

    context_manager = SynapseContextManager()

    # Demo different search scenarios
    scenarios = [
        {
            "name": "Debugging Scenario",
            "query": "rust error handling patterns",
            "description": "Looking for error handling examples in Rust code"
        },
        {
            "name": "Implementation Scenario",
            "query": "how to implement async authentication",
            "description": "Searching for async authentication implementation guides"
        },
        {
            "name": "Testing Scenario",
            "query": "python test coverage automation",
            "description": "Finding test coverage tools and patterns"
        },
        {
            "name": "Fuzzy Search Scenario",
            "query": "securty vulnerabilties",  # Intentional typos
            "description": "Testing fuzzy matching with typos"
        }
    ]

    for scenario in scenarios:
        print(f"\n📋 {scenario['name']}")
        print(f"💭 {scenario['description']}")
        print(f"🔍 Query: '{scenario['query']}'")

        # Perform search
        result = context_manager.intelligent_search(scenario['query'], max_results=3)

        # Display results
        print(f"🎯 Intent: {result.get('intent', 'unknown')}")
        print(f"📁 Results found: {result.get('nodes_found', 0)}")
        print(f"⚡ Source: {result.get('source', 'unknown')}")

        # Show query expansions
        if result.get('expanded_queries'):
            print(f"🔍 Top expansions: {', '.join(result['expanded_queries'][:2])}")

        # Show best matches
        context = result.get('context', {})
        primary_matches = context.get('primary_matches', [])

        if primary_matches:
            print(f"🏆 Top matches:")
            for i, match in enumerate(primary_matches[:2], 1):
                score = match.get('smart_score', 0)
                match_type = match.get('match_type', 'unknown')
                print(f"   {i}. {match['file']} (score: {score:.2f}, {match_type})")
                print(f"      📝 {match['summary'][:80]}...")

        # Show search strategy
        strategy = context.get('search_strategy', {})
        if strategy:
            print(f"📊 Search strategy: {strategy}")

        # Show suggested actions
        actions = context.get('suggested_actions', [])
        if actions:
            print(f"💡 Suggestions: {', '.join(actions[:2])}")

def interactive_demo():
    """Interactive search demo"""
    print("\n\n💬 Interactive Search Demo")
    print("-" * 30)
    print("Enter search queries to see enhanced search in action.")
    print("Type 'quit' to exit.\n")

    context_manager = SynapseContextManager()

    while True:
        try:
            query = input("🔍 Search query: ").strip()

            if query.lower() in ['quit', 'exit', 'q']:
                break

            if not query:
                continue

            print("\nSearching...")
            result = context_manager.intelligent_search(query, max_results=3)

            # Display condensed results
            print(f"🎯 Intent: {result.get('intent', 'unknown')}")
            print(f"📁 Found: {result.get('nodes_found', 0)} results")

            context = result.get('context', {})
            primary = context.get('primary_matches', [])

            if primary:
                print("🏆 Best match:")
                match = primary[0]
                print(f"   📄 {match['path']}")
                print(f"   💯 Score: {match.get('smart_score', 0):.2f}")
                print(f"   📝 {match['summary'][:100]}...")
            else:
                print("❌ No matches found")

            print()

        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"❌ Error: {e}\n")

    print("👋 Demo finished!")

def pretty_print_json(data, max_depth=3):
    """Pretty print JSON with limited depth"""
    def truncate_dict(obj, depth=0):
        if depth >= max_depth:
            return "..."
        if isinstance(obj, dict):
            return {k: truncate_dict(v, depth + 1) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [truncate_dict(item, depth + 1) for item in obj[:3]]  # Show first 3 items
        return obj

    truncated = truncate_dict(data)
    return json.dumps(truncated, indent=2)

def full_example():
    """Show a complete search example with all details"""
    print("\n\n📊 Complete Search Example")
    print("-" * 30)

    context_manager = SynapseContextManager()
    query = "implement rust async error handling"

    print(f"🔍 Query: '{query}'")
    print("\nPerforming enhanced search...")

    result = context_manager.intelligent_search(query, max_results=5)

    print("\n📋 Complete Result Structure:")
    print(pretty_print_json(result))

def main():
    """Run the complete demo"""
    print("🌟 Enhanced Search System Demo")
    print("=" * 50)

    try:
        demo_query_processor()
        demo_enhanced_search()
        full_example()

        # Ask if user wants interactive demo
        print("\n" + "=" * 50)
        response = input("🤔 Try interactive demo? (y/n): ").strip().lower()
        if response in ['y', 'yes']:
            interactive_demo()

    except Exception as e:
        print(f"\n❌ Demo failed: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()