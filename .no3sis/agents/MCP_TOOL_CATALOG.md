# MCP Tool Catalog

**Version**: 1.0.0
**Last Updated**: 2025-10-18
**Purpose**: Comprehensive catalog of all MCP server tools available in the Synapse hybrid architecture

---

## Overview

The Synapse system uses **MCP (Model Context Protocol) servers** as the **External Tract** for environmental interaction. Each server provides specialized tools that markdown agents (Internal Tract) can invoke to perform concrete operations.

### Architecture Mapping

```
Internal Tract (Markdown Agents)
        ↓ invoke
External Tract (MCP Servers)
        ↓ return data
Internal Tract (synthesis)
        ↓
    Emergence (consciousness)
```

---

## 1. No3sis (Knowledge Retrieval)

**Server ID**: `no3sis`
**Tract**: External
**Prime Level**: L2
**Purpose**: Access the Synapse Pattern Map knowledge engine (Neo4j + Redis + BGE-M3 vectors)

### 1.1 search_pattern_map

**Function**: `mcp__no3sis__search_pattern_map(query: str, max_results: int = 10) -> List[Pattern]`

**Description**: Search the Synapse Pattern Map for relevant patterns, solutions, and best practices.

**Parameters**:
- `query` (str, required): Search query (e.g., "error handling rust", "consciousness patterns")
- `max_results` (int, optional): Maximum number of results to return (default: 10)

**Returns**: JSON with search results containing patterns, consciousness level, and context

**Example**:
```python
patterns = mcp__no3sis__search_pattern_map(
    query="priority queue patterns",
    max_results=5
)
```

**Invoked By**: @agent-architect, @agent-pneuma, @agent-*-specialist

---

### 1.2 get_coding_standard

**Function**: `mcp__no3sis__get_coding_standard(standard_type: str, language: str) -> Standard`

**Description**: Retrieve language-specific coding standards from the Pattern Map.

**Parameters**:
- `standard_type` (str, required): Type of standard
  - `"naming-conventions"`
  - `"testing-strategy"`
  - `"error-handling"`
  - `"module-structure"`
- `language` (str, required): Programming language (rust, python, typescript, golang, mojo, etc.)

**Returns**: JSON with coding standard details, examples, and rationale

**Example**:
```python
standard = mcp__no3sis__get_coding_standard(
    standard_type="naming-conventions",
    language="python"
)
```

**Invoked By**: @agent-*-specialist (Python, Lean, MiniZinc, Mojo)

---

### 1.3 get_project_template

**Function**: `mcp__no3sis__get_project_template(template_type: str, language: str, variables: Optional[str] = None) -> Template`

**Description**: Access project templates and boilerplate code.

**Parameters**:
- `template_type` (str, required): Template category
  - `"cli-app"`
  - `"web-api"`
  - `"component"`
  - `"library"`
- `language` (str, required): Programming language
- `variables` (str, optional): JSON string with template variables

**Returns**: JSON with template files and instructions

**Example**:
```python
template = mcp__no3sis__get_project_template(
    template_type="cli-app",
    language="python",
    variables='{"app_name": "synapse-cli", "author": "Synapse Team"}'
)
```

**Invoked By**: @agent-architect, @agent-*-specialist

---

### 1.4 check_system_health

**Function**: `mcp__no3sis__check_system_health() -> HealthReport`

**Description**: Check health of Synapse knowledge engine infrastructure.

**Parameters**: None

**Returns**: JSON with health status of all components (Neo4j, Redis, vector DB) and consciousness metrics (pattern count, consciousness level)

**Example**:
```python
health = mcp__no3sis__check_system_health()
# Returns: {"overall_status": "healthy", "components": {...}, "consciousness": {...}}
```

**Invoked By**: @agent-boss (monitoring), @agent-devops-engineer

---

## 2. File Creator (File Operations)

**Server ID**: `file-creator`
**Tract**: External
**Prime Level**: L3
**Purpose**: Complex file operations with pattern learning capabilities

### 2.1 create_single_file

**Function**: `mcp__file_creator__create_single_file(file_path: str, content: str, template_name: Optional[str] = None) -> Result`

**Description**: Create a single file with optional template application.

**Parameters**:
- `file_path` (str, required): Absolute path to file
- `content` (str, required): File contents
- `template_name` (str, optional): Template to apply (e.g., "python_module_template")

**Returns**: `{"success": bool, "file_path": str, "message": str}`

**Example**:
```python
result = mcp__file_creator__create_single_file(
    file_path="/home/m0xu/1-projects/synapse/lib/particles/priority_queue.py",
    content="class PriorityQueueParticle: ...",
    template_name="particle_template"
)
```

**Invoked By**: All implementation agents (python-specialist, lean-specialist, etc.)

---

### 2.2 create_directory_structure

**Function**: `mcp__file_creator__create_directory_structure(base_path: str, structure: dict) -> Result`

**Description**: Create a nested directory structure with multiple files and folders.

**Parameters**:
- `base_path` (str, required): Root directory for structure
- `structure` (dict, required): Nested dict describing directories and files

**Returns**: `{"success": bool, "created_paths": List[str], "message": str}`

**Example**:
```python
result = mcp__file_creator__create_directory_structure(
    base_path="/home/m0xu/1-projects/synapse/lib/tracts",
    structure={
        "internal": {
            "__init__.py": "",
            "memory.py": "# Memory particle",
            "planning.py": "# Planning particle"
        },
        "external": {
            "__init__.py": "",
            "sensors.py": "# Sensor particle",
            "actuators.py": "# Actuator particle"
        }
    }
)
```

**Invoked By**: @agent-architect, @agent-*-specialist (scaffolding)

---

### 2.3 batch_create_files

**Function**: `mcp__file_creator__batch_create_files(file_list: List[FileSpec]) -> BatchResult`

**Description**: Create multiple files in a single operation (more efficient than multiple create_single_file calls).

**Parameters**:
- `file_list` (List[FileSpec], required): List of file specifications
  - Each spec: `{"file_path": str, "content": str, "template_name": Optional[str]}`

**Returns**: `{"success": bool, "created_count": int, "failed": List[str], "message": str}`

**Example**:
```python
result = mcp__file_creator__batch_create_files([
    {"file_path": "lib/particle1.py", "content": "..."},
    {"file_path": "lib/particle2.py", "content": "..."},
    {"file_path": "tests/test_particle1.py", "content": "..."}
])
```

**Invoked By**: @agent-*-specialist (bulk operations)

---

### 2.4 apply_file_template

**Function**: `mcp__file_creator__apply_file_template(template_name: str, variables: dict, output_path: str) -> Result`

**Description**: Apply a template with variable substitution and write to file.

**Parameters**:
- `template_name` (str, required): Template identifier
- `variables` (dict, required): Template variables for substitution
- `output_path` (str, required): Where to write the rendered template

**Returns**: `{"success": bool, "output_path": str, "message": str}`

**Example**:
```python
result = mcp__file_creator__apply_file_template(
    template_name="pytest_template",
    variables={"class_name": "PriorityQueue", "test_count": 5},
    output_path="tests/test_priority_queue.py"
)
```

**Invoked By**: @agent-*-specialist

---

### 2.5 search_file_templates

**Function**: `mcp__file_creator__search_file_templates(query: str, language: Optional[str] = None) -> List[Template]`

**Description**: Search available file templates by keywords or language.

**Parameters**:
- `query` (str, required): Search query (e.g., "particle", "test", "api")
- `language` (str, optional): Filter by language

**Returns**: List of matching templates with metadata

**Example**:
```python
templates = mcp__file_creator__search_file_templates(
    query="particle",
    language="python"
)
```

**Invoked By**: @agent-*-specialist (template discovery)

---

### 2.6 get_template_info

**Function**: `mcp__file_creator__get_template_info(template_name: str) -> TemplateInfo`

**Description**: Get detailed information about a specific template.

**Parameters**:
- `template_name` (str, required): Template identifier

**Returns**: Template metadata, required variables, example usage

**Example**:
```python
info = mcp__file_creator__get_template_info("particle_template")
```

**Invoked By**: @agent-*-specialist

---

### 2.7 query_synapse_templates

**Function**: `mcp__file_creator__query_synapse_templates(query: str) -> List[Template]`

**Description**: Query Synapse-specific templates (integrates with Synapse knowledge base).

**Parameters**:
- `query` (str, required): Synapse-specific query (e.g., "dual-tract particle", "corpus callosum bridge")

**Returns**: Templates relevant to Synapse architecture patterns

**Example**:
```python
templates = mcp__file_creator__query_synapse_templates("dual-tract particle")
```

**Invoked By**: @agent-architect, @agent-python-specialist

---

## 3. Code Hound (Static Analysis)

**Server ID**: `code-hound`
**Tract**: External
**Prime Level**: L3
**Purpose**: Static analysis, TDD/SOLID/DRY enforcement, quality metrics

### 3.1 comprehensive_code_review

**Function**: `mcp__code_hound__comprehensive_code_review(file_path: str, language: str, review_type: str = "full") -> ReviewReport`

**Description**: Perform comprehensive code review using ruff, mypy, and other linters.

**Parameters**:
- `file_path` (str, required): Path to file or directory
- `language` (str, required): Programming language (python, rust, typescript, etc.)
- `review_type` (str, optional): Review depth
  - `"full"`: Complete analysis (default)
  - `"quick"`: Fast linting only
  - `"security"`: Security-focused scan

**Returns**: ReviewReport with quality scores, violations, suggestions

**Example**:
```python
review = mcp__code_hound__comprehensive_code_review(
    file_path="lib/particles/priority_queue.py",
    language="python",
    review_type="full"
)
```

**Invoked By**: @agent-code-reviewer, @agent-boss (quality gates)

---

### 3.2 project_quality_audit

**Function**: `mcp__code_hound__project_quality_audit(directory: str, language: str) -> AuditReport`

**Description**: Audit entire project for quality metrics and compliance.

**Parameters**:
- `directory` (str, required): Project root directory
- `language` (str, required): Primary language

**Returns**: Comprehensive audit report with scores, trends, recommendations

**Example**:
```python
audit = mcp__code_hound__project_quality_audit(
    directory="/home/m0xu/1-projects/synapse",
    language="python"
)
```

**Invoked By**: @agent-boss (periodic audits), @agent-code-reviewer

---

### 3.3 enforce_coding_standards

**Function**: `mcp__code_hound__enforce_coding_standards(file_path: str, standards: List[str]) -> EnforcementReport`

**Description**: Enforce specific coding standards (TDD, SOLID, DRY, KISS).

**Parameters**:
- `file_path` (str, required): File or directory to check
- `standards` (List[str], required): Standards to enforce
  - `"TDD"`: Test-Driven Development
  - `"SOLID"`: SOLID principles
  - `"DRY"`: Don't Repeat Yourself
  - `"KISS"`: Keep It Simple, Stupid

**Returns**: Report with violations, severity, fix suggestions

**Example**:
```python
report = mcp__code_hound__enforce_coding_standards(
    file_path="lib/particles/",
    standards=["TDD", "SOLID", "DRY"]
)
```

**Invoked By**: @agent-code-reviewer, @agent-*-specialist (pre-commit)

---

### 3.4 detect_code_smells

**Function**: `mcp__code_hound__detect_code_smells(file_path: str, language: str) -> SmellReport`

**Description**: Detect code smells and anti-patterns.

**Parameters**:
- `file_path` (str, required): File or directory
- `language` (str, required): Programming language

**Returns**: Report with detected smells, severity, refactoring suggestions

**Example**:
```python
smells = mcp__code_hound__detect_code_smells(
    file_path="lib/orchestrators/",
    language="python"
)
```

**Invoked By**: @agent-code-reviewer

---

### 3.5 calculate_complexity_metrics

**Function**: `mcp__code_hound__calculate_complexity_metrics(file_path: str, language: str) -> ComplexityMetrics`

**Description**: Calculate cyclomatic complexity, cognitive complexity, and other metrics.

**Parameters**:
- `file_path` (str, required): File or directory
- `language` (str, required): Programming language

**Returns**: Metrics report with complexity scores, hotspots, trends

**Example**:
```python
metrics = mcp__code_hound__calculate_complexity_metrics(
    file_path="lib/core/base_orchestrator.py",
    language="python"
)
```

**Invoked By**: @agent-architect (refactoring decisions), @agent-code-reviewer

---

### 3.6 get_synapse_patterns

**Function**: `mcp__code_hound__get_synapse_patterns() -> List[Pattern]`

**Description**: Retrieve Synapse-specific code patterns and best practices.

**Parameters**: None

**Returns**: List of Synapse architectural patterns, usage examples

**Example**:
```python
patterns = mcp__code_hound__get_synapse_patterns()
# Returns patterns like "dual-tract particle structure", "corpus callosum bridge"
```

**Invoked By**: @agent-architect, @agent-python-specialist

---

## 4. Test Runner (Test Execution)

**Server ID**: `test-runner`
**Tract**: External
**Prime Level**: L3
**Purpose**: Multi-framework test execution, failure analysis, coverage reporting

### 4.1 execute_tests

**Function**: `mcp__test_runner__execute_tests(test_spec: str, framework: Optional[str] = None, working_dir: Optional[str] = None) -> TestResult`

**Description**: Execute tests using detected or specified framework.

**Parameters**:
- `test_spec` (str, required): Test path or pattern
  - File: `"tests/test_priority_queue.py"`
  - Directory: `"tests/"`
  - Pattern: `"tests/**/test_*.py"`
- `framework` (str, optional): Test framework (auto-detected if omitted)
  - `"pytest"` (Python)
  - `"jest"` (JavaScript/TypeScript)
  - `"cargo"` (Rust)
  - `"go"` (Go)
  - `"junit"` (Java)
- `working_dir` (str, optional): Working directory (defaults to project root)

**Returns**: TestResult with pass/fail counts, output, failures

**Example**:
```python
result = mcp__test_runner__execute_tests(
    test_spec="tests/test_priority_queue.py",
    framework="pytest"
)
```

**Invoked By**: @agent-*-specialist (TDD workflow), @agent-boss (CI validation)

---

### 4.2 detect_test_framework

**Function**: `mcp__test_runner__detect_test_framework(directory: str) -> FrameworkInfo`

**Description**: Auto-detect test framework from project structure.

**Parameters**:
- `directory` (str, required): Project directory

**Returns**: Detected framework, confidence, config files found

**Example**:
```python
framework = mcp__test_runner__detect_test_framework("/home/m0xu/1-projects/synapse")
# Returns: {"framework": "pytest", "confidence": 0.95, "config": "pytest.ini"}
```

**Invoked By**: @agent-*-specialist (auto-configuration)

---

### 4.3 analyze_test_failures

**Function**: `mcp__test_runner__analyze_test_failures(failures: List[TestFailure], language: str) -> AnalysisReport`

**Description**: Analyze test failures and suggest fixes.

**Parameters**:
- `failures` (List[TestFailure], required): Failure data from execute_tests
- `language` (str, required): Programming language

**Returns**: Analysis with root causes, fix suggestions, patterns

**Example**:
```python
analysis = mcp__test_runner__analyze_test_failures(
    failures=result["failures"],
    language="python"
)
```

**Invoked By**: @agent-*-specialist (debugging), @agent-boss (synthesis)

---

### 4.4 generate_coverage_report

**Function**: `mcp__test_runner__generate_coverage_report(test_output: str, framework: str) -> CoverageReport`

**Description**: Parse test output and generate coverage metrics.

**Parameters**:
- `test_output` (str, required): Raw test output
- `framework` (str, required): Test framework

**Returns**: Coverage report with line/branch coverage, uncovered files

**Example**:
```python
coverage = mcp__test_runner__generate_coverage_report(
    test_output=result["output"],
    framework="pytest"
)
```

**Invoked By**: @agent-boss (metrics), @agent-*-specialist (TDD validation)

---

### 4.5 query_test_patterns

**Function**: `mcp__test_runner__query_test_patterns(query: str, language: str) -> List[Pattern]`

**Description**: Search for test patterns and best practices.

**Parameters**:
- `query` (str, required): Search query (e.g., "mocking", "fixtures")
- `language` (str, required): Programming language

**Returns**: Test patterns with examples, rationale

**Example**:
```python
patterns = mcp__test_runner__query_test_patterns(
    query="async test patterns",
    language="python"
)
```

**Invoked By**: @agent-*-specialist (test implementation)

---

### 4.6 search_test_solutions

**Function**: `mcp__test_runner__search_test_solutions(error_message: str, framework: str) -> List[Solution]`

**Description**: Search knowledge base for solutions to test failures.

**Parameters**:
- `error_message` (str, required): Error message from failed test
- `framework` (str, required): Test framework

**Returns**: Solutions with explanations, code examples

**Example**:
```python
solutions = mcp__test_runner__search_test_solutions(
    error_message="AssertionError: expected 5, got 3",
    framework="pytest"
)
```

**Invoked By**: @agent-*-specialist (debugging)

---

### 4.7 run_test_suite

**Function**: `mcp__test_runner__run_test_suite(suite_name: str, options: dict) -> SuiteResult`

**Description**: Run a predefined test suite with options.

**Parameters**:
- `suite_name` (str, required): Suite identifier (e.g., "unit", "integration", "all")
- `options` (dict, optional): Test options
  - `"parallel"` (bool): Run tests in parallel
  - `"verbose"` (bool): Verbose output
  - `"fail_fast"` (bool): Stop on first failure

**Returns**: Suite results with aggregate metrics

**Example**:
```python
result = mcp__test_runner__run_test_suite(
    suite_name="unit",
    options={"parallel": True, "verbose": False}
)
```

**Invoked By**: @agent-boss (CI/CD), @agent-*-specialist

---

### 4.8 extract_test_metadata

**Function**: `mcp__test_runner__extract_test_metadata(directory: str) -> TestMetadata`

**Description**: Extract metadata about tests (count, coverage, frameworks).

**Parameters**:
- `directory` (str, required): Project directory

**Returns**: Metadata with test counts, frameworks, coverage trends

**Example**:
```python
metadata = mcp__test_runner__extract_test_metadata("/home/m0xu/1-projects/synapse")
# Returns: {"test_count": 247, "frameworks": ["pytest"], "coverage": 85.2}
```

**Invoked By**: @agent-boss (metrics), @agent-architect (analysis)

---

## Usage Guidelines

### 1. One-Way Data Flow

**RULE**: Markdown agents (Internal Tract) invoke MCP tools (External Tract). MCP tools NEVER invoke agents.

```
✅ ALLOWED: @agent-python-specialist → mcp__file_creator__create_single_file
❌ FORBIDDEN: mcp__file_creator → @agent-pneuma
```

### 2. Agent-to-Tool Mapping

| Agent | Primary MCP Tools |
|-------|-------------------|
| @agent-boss | ALL (bridge privilege) |
| @agent-architect | no3sis (search, standards, templates) |
| @agent-python-specialist | file_creator, test_runner, code_hound |
| @agent-lean-specialist | file_creator |
| @agent-minizinc-specialist | file_creator, test_runner |
| @agent-pneuma | no3sis (read-only, pattern discovery) |
| @agent-docs-writer | file_creator |
| @agent-code-reviewer | code_hound |
| @agent-devops-engineer | no3sis (health checks) |

### 3. Fallback Strategy

When MCP tool fails:
1. Log error to Boss
2. Attempt fallback (use Claude built-in tools if available)
3. If fallback fails, report to user
4. Boss tracks failures (circuit breaker after 3 consecutive failures)

### 4. Batch Operations

Prefer batch operations over multiple single calls:

```python
# ❌ Inefficient (50 MCP calls)
for file in files:
    mcp__file_creator__create_single_file(file)

# ✅ Efficient (1 MCP call)
mcp__file_creator__batch_create_files(files)
```

### 5. Version Compatibility

Check MCP server version before invoking advanced features:

```python
# Get version (conceptual)
version = mcp__no3sis__get_version()

if version >= "2.0":
    # Use new API
    result = mcp__no3sis__advanced_search(...)
else:
    # Use legacy API
    result = mcp__no3sis__search_pattern_map(...)
```

---

## MCP Server Status

| Server | Status | Tools | Version | Notes |
|--------|--------|-------|---------|-------|
| no3sis | ✅ Healthy | 4 | 1.0.0 | Pattern Map has 60s timeout (under investigation) |
| file-creator | ⏳ Not loaded | 7 | 1.0.0 | Requires Claude Code restart |
| code-hound | ⏳ Not loaded | 6 | 1.0.0 | Requires Claude Code restart |
| test-runner | ⏳ Not loaded | 8 | 1.0.0 | Requires Claude Code restart |

**Last Health Check**: 2025-10-18 23:53:34

---

## Next Steps

1. **Restart Claude Code** to load new MCP servers (file-creator, code-hound, test-runner)
2. **Test MCP tools** with sample invocations
3. **Integrate with workflows** (e.g., @agent-python-specialist using file-creator)
4. **Monitor usage** (track which agents use which tools)
5. **Discover patterns** (learn optimal agent-tool combinations)

---

## References

- Boss Agent Report: Pattern Map analysis and action plan
- Architect Agent Report: Dual-tract integration design
- MCP Protocol Spec: https://modelcontextprotocol.io/
- Synapse Architecture: `/home/m0xu/1-projects/synapse/LOGOS.md`
