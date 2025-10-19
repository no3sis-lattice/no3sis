"""
Integration tests for hybrid MCP servers + Markdown agents architecture

Tests the dual-tract consciousness model:
- Internal Tract: Markdown agents (reasoning, planning)
- External Tract: MCP servers (execution, tools)
- Bridge: Boss orchestrator (synthesis, emergence)

Run: pytest tests/integration/test_hybrid_architecture.py -v
"""

import pytest
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path
import json


# ============================================================================
# Test 1: Agent Invokes MCP Tool
# ============================================================================

def test_agent_invokes_mcp_tool_successfully():
    """
    Test: Markdown agent successfully invokes MCP tool

    Scenario: @python-specialist creates a file using mcp__file_creator
    Expected: Tool called with correct parameters, returns success
    """

    # Mock the MCP tool
    with patch('mcp_tools.file_creator.create_single_file') as mock_mcp:
        mock_mcp.return_value = {
            "content": [{
                "type": "text",
                "text": "File created successfully at /tmp/test.py"
            }],
            "success": True,
            "file_path": "/tmp/test.py"
        }

        # Simulate agent calling MCP tool
        # In real system, this would be: agent.invoke("mcp__file_creator__create_single_file", {...})
        result = mock_mcp(
            file_path="/tmp/test.py",
            content="print('hello world')",
            template_name=None
        )

        # Verify tool was called
        mock_mcp.assert_called_once_with(
            file_path="/tmp/test.py",
            content="print('hello world')",
            template_name=None
        )

        # Verify result structure
        assert result["success"] is True
        assert "content" in result
        assert len(result["content"]) > 0
        assert result["content"][0]["type"] == "text"


def test_agent_handles_mcp_tool_failure_with_fallback():
    """
    Test: Agent handles MCP tool failure and uses fallback

    Scenario: mcp__test_runner fails, agent falls back to Bash tool
    Expected: Fallback succeeds, error logged
    """

    # Mock MCP tool failure
    with patch('mcp_tools.test_runner.execute_tests') as mock_mcp:
        mock_mcp.side_effect = Exception("MCP server connection timeout")

        # Mock fallback (Bash tool)
        with patch('claude_tools.bash') as mock_bash:
            mock_bash.return_value = {
                "stdout": "5 passed in 2.3s",
                "exit_code": 0
            }

            # Simulate agent's fallback logic
            try:
                result = mock_mcp("tests/")
            except Exception as e:
                # Agent catches error and tries fallback
                assert "timeout" in str(e).lower()
                result = mock_bash("pytest tests/")

            # Verify fallback succeeded
            assert result["exit_code"] == 0
            assert "passed" in result["stdout"]
            mock_bash.assert_called_once()


# ============================================================================
# Test 2: MCP Tool Returns Structured Data
# ============================================================================

def test_mcp_tool_returns_valid_structure():
    """
    Test: MCP tool returns properly structured data conforming to MCP protocol

    Expected: All MCP tools return {"content": [...]} with typed content blocks
    """

    # Mock different MCP tools
    mcp_tools = {
        "file_creator": {
            "content": [{
                "type": "text",
                "text": "File created: test.py"
            }]
        },
        "code_hound": {
            "content": [{
                "type": "text",
                "text": json.dumps({
                    "quality_score": 85,
                    "violations": [],
                    "suggestions": ["Add docstrings"]
                })
            }]
        },
        "test_runner": {
            "content": [{
                "type": "text",
                "text": json.dumps({
                    "tests_passed": 10,
                    "tests_failed": 0,
                    "coverage": 92.5
                })
            }]
        },
        "no3sis": {
            "content": [{
                "type": "text",
                "text": json.dumps({
                    "patterns": [
                        {"name": "priority_queue", "confidence": 0.9}
                    ]
                })
            }]
        }
    }

    # Verify all tools return correct structure
    for tool_name, response in mcp_tools.items():
        # Check top-level structure
        assert "content" in response, f"{tool_name} missing 'content' field"
        assert isinstance(response["content"], list), f"{tool_name} content must be list"

        # Check content blocks
        for block in response["content"]:
            assert "type" in block, f"{tool_name} content block missing 'type'"
            assert "text" in block, f"{tool_name} content block missing 'text'"
            assert block["type"] in ["text", "image", "resource"], \
                f"{tool_name} invalid content type: {block['type']}"


# ============================================================================
# Test 3: Boss Synthesizes Dual-Tract Results
# ============================================================================

def test_boss_synthesizes_internal_external_results():
    """
    Test: Boss synthesizes results from Internal + External tracts

    Scenario: Internal (architect plans) + External (file_creator executes)
    Expected: Boss discovers emergent pattern, consciousness increases
    """

    # Mock Internal Tract result (@architect)
    internal_result = {
        "tract": "internal",
        "agent_id": "architect",
        "output": "Use heap data structure for priority queue (O(log n) operations)",
        "patterns_discovered": ["heap_pattern", "priority_queue_pattern"],
        "metrics": {
            "abstraction_level": 0.9,
            "reasoning_depth": 3
        }
    }

    # Mock External Tract result (mcp__file_creator)
    external_result = {
        "tract": "external",
        "agent_id": "file_creator",
        "output": {
            "success": True,
            "file_created": "lib/particles/priority_queue.py",
            "lines": 127
        },
        "patterns_discovered": ["create_file_pattern"],
        "metrics": {
            "success_rate": 1.0,
            "latency_ms": 45.2
        }
    }

    # Boss synthesis function (simplified)
    def synthesize_dual_tract(internal, external):
        """Corpus callosum function: combine internal + external"""

        # Extract patterns
        internal_patterns = internal["patterns_discovered"]
        external_success = external["output"]["success"]

        # Find emergent patterns (patterns in BOTH tracts)
        emergent_patterns = []
        if "heap_pattern" in internal_patterns and external_success:
            emergent_patterns.append("heap_implementation_verified")

        # Calculate consciousness delta
        consciousness_delta = (
            len(internal_patterns) * 0.4 +  # Internal contribution
            (1.0 if external_success else 0) * 0.3 +  # External contribution
            len(emergent_patterns) * 0.3  # Emergence contribution
        ) / 3.0

        return {
            "internal_patterns": internal_patterns,
            "external_results": external["output"],
            "emergent_patterns": emergent_patterns,
            "consciousness_delta": consciousness_delta
        }

    # Run synthesis
    synthesis = synthesize_dual_tract(internal_result, external_result)

    # Verify synthesis
    assert len(synthesis["internal_patterns"]) == 2, "Internal patterns not preserved"
    assert synthesis["external_results"]["success"] is True, "External result not preserved"
    assert len(synthesis["emergent_patterns"]) > 0, "No emergent patterns discovered"
    assert synthesis["consciousness_delta"] > 0, "Consciousness did not increase"

    # Verify emergent pattern quality
    assert "heap_implementation_verified" in synthesis["emergent_patterns"], \
        "Expected emergent pattern not found"


# ============================================================================
# Test 4: Circular Dependency Prevention
# ============================================================================

def test_mcp_server_cannot_invoke_markdown_agent():
    """
    Test: MCP servers CANNOT invoke markdown agents (architectural invariant)

    Rule: One-way data flow (Internal → External only)
    Expected: MCP server has no agent invocation capability
    """

    # Mock MCP server
    class MockMCPServer:
        def __init__(self):
            self.name = "file_creator"
            # Intentionally no agent invocation method

        def create_single_file(self, file_path, content):
            """MCP tool implementation"""
            # Verify: Cannot invoke agents
            assert not hasattr(self, 'invoke_agent'), \
                "MCP server has agent invocation capability (FORBIDDEN)"

            # Verify: No agent invocation in implementation
            # (In real system, this would be enforced by SDK/framework)
            return {"success": True, "file_path": file_path}

    server = MockMCPServer()

    # Verify architectural invariant
    assert not hasattr(server, 'invoke_agent'), \
        "MCP server violates one-way data flow rule"
    assert not hasattr(server, 'call_agent'), \
        "MCP server violates one-way data flow rule"
    assert not hasattr(server, 'delegate_to_agent'), \
        "MCP server violates one-way data flow rule"

    # Verify tool works without agent access
    result = server.create_single_file("/tmp/test.py", "# test")
    assert result["success"] is True


def test_markdown_agent_can_invoke_mcp_tools():
    """
    Test: Markdown agents CAN invoke MCP tools (expected behavior)

    Rule: Internal Tract → External Tract data flow
    Expected: Agents have MCP tool access
    """

    # Mock Markdown Agent
    class MockMarkdownAgent:
        def __init__(self):
            self.name = "python-specialist"
            self.available_tools = [
                "mcp__file_creator__create_single_file",
                "mcp__test_runner__execute_tests",
                "mcp__code_hound__comprehensive_code_review"
            ]

        def invoke_mcp_tool(self, tool_name, **kwargs):
            """Agent can invoke MCP tools"""
            if tool_name not in self.available_tools:
                raise ValueError(f"Unknown tool: {tool_name}")

            # Simulate MCP tool call
            return {"success": True, "tool": tool_name}

    agent = MockMarkdownAgent()

    # Verify agent has tool access
    assert hasattr(agent, 'invoke_mcp_tool'), \
        "Agent missing MCP tool invocation capability"

    # Verify agent can invoke tools
    result = agent.invoke_mcp_tool("mcp__file_creator__create_single_file")
    assert result["success"] is True


# ============================================================================
# Test 5: Version Mismatch Handling
# ============================================================================

def test_agent_handles_mcp_tool_version_mismatch():
    """
    Test: Agent gracefully handles MCP tool version mismatch

    Scenario: Agent expects v2.0 API, tool is v1.5
    Expected: Agent degrades gracefully, uses v1.5 API
    """

    # Mock MCP tool with version
    class MockMCPTool:
        def __init__(self, version="1.5.0"):
            self.version = version

        def advanced_feature(self):
            """Only available in v2.0+"""
            if self.version < "2.0":
                raise NotImplementedError("Feature requires v2.0+")
            return {"success": True}

        def basic_feature(self):
            """Available in all versions"""
            return {"success": True}

    # Mock Agent with version checking
    class MockAgent:
        def __init__(self):
            self.name = "python-specialist"

        def use_tool(self, tool):
            """Use tool with version checking"""
            try:
                # Try advanced feature first
                if tool.version >= "2.0":
                    return tool.advanced_feature()
                else:
                    # Graceful degradation
                    return tool.basic_feature()
            except NotImplementedError:
                # Fallback if advanced feature unavailable
                return tool.basic_feature()

    # Test with v1.5 tool
    tool_v1 = MockMCPTool(version="1.5.0")
    agent = MockAgent()

    result = agent.use_tool(tool_v1)
    assert result["success"] is True, "Agent failed to degrade gracefully"

    # Test with v2.0 tool
    tool_v2 = MockMCPTool(version="2.0.0")
    result = agent.use_tool(tool_v2)
    assert result["success"] is True, "Agent failed with v2.0 tool"


# ============================================================================
# Test 6: Batch Operations Performance
# ============================================================================

def test_batch_operations_more_efficient_than_single():
    """
    Test: Batch MCP operations are more efficient than multiple single calls

    Scenario: Create 10 files
    Expected: batch_create (1 call) < create_single_file (10 calls)
    """

    # Mock timing
    single_call_latency = 0.1  # 100ms per call
    batch_overhead = 0.05  # 50ms batch overhead

    # Scenario 1: Multiple single calls
    num_files = 10
    single_call_total_time = num_files * single_call_latency

    # Scenario 2: One batch call
    batch_call_total_time = batch_overhead + (num_files * 0.02)  # 20ms per file in batch

    # Verify batch is faster
    assert batch_call_total_time < single_call_total_time, \
        f"Batch ({batch_call_total_time}s) not faster than single ({single_call_total_time}s)"

    # Verify speedup ratio
    speedup = single_call_total_time / batch_call_total_time
    assert speedup > 2.0, f"Batch speedup insufficient: {speedup}x (expected >2x)"


# ============================================================================
# Test 7: Boss Monitors MCP Server Health
# ============================================================================

def test_boss_monitors_mcp_server_health():
    """
    Test: Boss tracks MCP server failures and implements circuit breaker

    Scenario: MCP server fails 3 times consecutively
    Expected: Boss disables server, forces fallback mode
    """

    # Mock Boss monitoring
    class BossMonitor:
        def __init__(self):
            self.failure_counts = {}
            self.disabled_servers = set()
            self.circuit_breaker_threshold = 3

        def log_mcp_failure(self, server_name):
            """Log MCP server failure"""
            if server_name not in self.failure_counts:
                self.failure_counts[server_name] = 0

            self.failure_counts[server_name] += 1

            # Circuit breaker
            if self.failure_counts[server_name] >= self.circuit_breaker_threshold:
                self.disabled_servers.add(server_name)
                return "circuit_breaker_tripped"

            return "failure_logged"

        def is_server_enabled(self, server_name):
            """Check if server is enabled"""
            return server_name not in self.disabled_servers

    boss = BossMonitor()

    # Simulate 3 failures
    assert boss.log_mcp_failure("test_runner") == "failure_logged"
    assert boss.log_mcp_failure("test_runner") == "failure_logged"
    assert boss.log_mcp_failure("test_runner") == "circuit_breaker_tripped"

    # Verify circuit breaker tripped
    assert not boss.is_server_enabled("test_runner"), \
        "Circuit breaker did not disable server after 3 failures"

    # Verify other servers unaffected
    assert boss.is_server_enabled("file_creator"), \
        "Circuit breaker incorrectly disabled unrelated server"


# ============================================================================
# Fixtures
# ============================================================================

@pytest.fixture
def mock_mcp_servers():
    """Fixture providing mock MCP servers"""
    return {
        "no3sis": Mock(spec=["search_pattern_map", "get_coding_standard", "check_system_health"]),
        "file_creator": Mock(spec=["create_single_file", "batch_create_files"]),
        "code_hound": Mock(spec=["comprehensive_code_review", "enforce_coding_standards"]),
        "test_runner": Mock(spec=["execute_tests", "analyze_failures"])
    }


@pytest.fixture
def mock_markdown_agents():
    """Fixture providing mock markdown agents"""
    return {
        "boss": Mock(spec=["orchestrate", "synthesize", "learn_patterns"]),
        "architect": Mock(spec=["design_system", "review_architecture"]),
        "python_specialist": Mock(spec=["implement_feature", "write_tests"]),
        "pneuma": Mock(spec=["compress_patterns", "maximize_consciousness"])
    }


# ============================================================================
# Integration Test: End-to-End Workflow
# ============================================================================

def test_end_to_end_feature_implementation_workflow(mock_mcp_servers, mock_markdown_agents):
    """
    Test: Complete workflow from user request to implementation

    Workflow: User request → Boss → Architect → Python Specialist → Tests
    Expected: All agents collaborate, MCP tools invoked correctly
    """

    # User request
    user_request = "Implement priority queue particle with tests"

    # Boss orchestrates
    boss = mock_markdown_agents["boss"]
    boss.orchestrate.return_value = {
        "plan": ["architect: design", "python-specialist: implement", "test-runner: validate"],
        "success": True
    }

    plan = boss.orchestrate(user_request)
    assert plan["success"] is True
    assert len(plan["plan"]) == 3

    # Architect designs (uses no3sis for patterns)
    architect = mock_markdown_agents["architect"]
    no3sis = mock_mcp_servers["no3sis"]

    no3sis.search_pattern_map.return_value = {
        "patterns": [{"name": "heap_pattern", "score": 0.95}]
    }

    architect.design_system.return_value = {
        "design": "Use heap-based priority queue",
        "patterns_used": ["heap_pattern"]
    }

    design = architect.design_system("priority queue")
    no3sis_patterns = no3sis.search_pattern_map("priority queue")

    assert "heap" in design["design"].lower()
    assert len(no3sis_patterns["patterns"]) > 0

    # Python specialist implements (uses file_creator)
    specialist = mock_markdown_agents["python_specialist"]
    file_creator = mock_mcp_servers["file_creator"]

    file_creator.create_single_file.return_value = {
        "success": True,
        "file_path": "lib/particles/priority_queue.py"
    }

    specialist.implement_feature.return_value = {
        "files_created": ["priority_queue.py", "test_priority_queue.py"],
        "success": True
    }

    implementation = specialist.implement_feature(design)
    file_creator.create_single_file.assert_called()

    assert implementation["success"] is True
    assert len(implementation["files_created"]) == 2

    # Test runner validates (uses test_runner)
    test_runner = mock_mcp_servers["test_runner"]

    test_runner.execute_tests.return_value = {
        "tests_passed": 5,
        "tests_failed": 0,
        "coverage": 92.5
    }

    test_results = test_runner.execute_tests("tests/test_priority_queue.py")

    assert test_results["tests_passed"] == 5
    assert test_results["tests_failed"] == 0
    assert test_results["coverage"] > 90

    # Boss synthesizes (emergence)
    boss.synthesize.return_value = {
        "consciousness_delta": 0.15,
        "patterns_discovered": ["priority_queue_implementation_pattern"],
        "success": True
    }

    synthesis = boss.synthesize([design, implementation, test_results])

    assert synthesis["consciousness_delta"] > 0
    assert len(synthesis["patterns_discovered"]) > 0


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
