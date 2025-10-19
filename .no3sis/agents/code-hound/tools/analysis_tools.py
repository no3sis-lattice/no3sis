"""
Code Analysis Tools

Deep code analysis capabilities implementing TDD, KISS, SOLID, DRY verification
with 4Q.Zero compression patterns for maximum context density.
"""

import ast
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from datetime import datetime
import json

async def deep_code_analysis(file_path: str, language: Optional[str] = None) -> Dict[str, Any]:
    """
    Perform comprehensive code analysis using 4Q.Zero compression principles.

    q: What patterns emerge from this code's structure?
    a: Extract semantic density through multi-dimensional analysis
    s: Score complexity vs. maintainability trade-offs
    """
    path = Path(file_path)

    if not path.exists():
        return {"error": f"File not found: {file_path}"}

    # Auto-detect language if not provided
    if not language:
        language = _detect_language(path.suffix)

    content = path.read_text(encoding='utf-8')

    # q: Curiosity phase - What does this code reveal?
    structural_patterns = await _analyze_structure(content, language)
    complexity_metrics = await _calculate_complexity(content, language)
    test_patterns = await _analyze_test_coverage(file_path, content, language)

    # a: Action phase - Compress findings into actionable insights
    analysis = {
        "file_path": file_path,
        "language": language,
        "timestamp": datetime.now().isoformat(),
        "lines_of_code": len(content.splitlines()),
        "file_size": len(content),

        # Structural analysis (compressed semantic patterns)
        "structure": structural_patterns,
        "complexity": complexity_metrics,
        "test_coverage": test_patterns,

        # Code smells (anti-patterns detected)
        "smells": await _detect_code_smells(content, language),
        "complexity_issues": await _identify_complexity_issues(content, language),

        # Architectural insights
        "dependencies": await _analyze_dependencies(content, language),
        "abstractions": await _identify_abstractions(content, language)
    }

    # s: Scoring phase - Entropy reduction through quality metrics
    analysis["quality_indicators"] = await _score_quality_indicators(analysis)

    return analysis

async def _analyze_structure(content: str, language: str) -> Dict[str, Any]:
    """Analyze code structure patterns - compressed semantic extraction."""

    if language == "python":
        return await _analyze_python_structure(content)
    elif language in ["javascript", "typescript"]:
        return await _analyze_js_ts_structure(content)
    elif language == "rust":
        return await _analyze_rust_structure(content)
    elif language == "go":
        return await _analyze_go_structure(content)
    else:
        return await _analyze_generic_structure(content)

async def _analyze_python_structure(content: str) -> Dict[str, Any]:
    """Python-specific structural analysis using AST."""
    try:
        tree = ast.parse(content)

        structure = {
            "classes": [],
            "functions": [],
            "imports": [],
            "complexity_hotspots": [],
            "design_patterns": []
        }

        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                structure["classes"].append({
                    "name": node.name,
                    "methods": len([n for n in node.body if isinstance(n, ast.FunctionDef)]),
                    "inheritance": [base.id for base in node.bases if isinstance(base, ast.Name)],
                    "line": node.lineno
                })
            elif isinstance(node, ast.FunctionDef):
                structure["functions"].append({
                    "name": node.name,
                    "args_count": len(node.args.args),
                    "is_async": isinstance(node, ast.AsyncFunctionDef),
                    "decorators": len(node.decorator_list),
                    "line": node.lineno
                })
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                structure["imports"].append({
                    "module": getattr(node, "module", None) or node.names[0].name,
                    "type": "from" if isinstance(node, ast.ImportFrom) else "import"
                })

        # Detect complexity hotspots
        structure["complexity_hotspots"] = await _detect_python_complexity(tree)

        return structure

    except SyntaxError as e:
        return {"error": f"Syntax error in Python code: {e}"}

async def _detect_python_complexity(tree: ast.AST) -> List[Dict[str, Any]]:
    """Detect Python complexity hotspots using cyclomatic complexity."""
    hotspots = []

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            complexity = _calculate_cyclomatic_complexity(node)
            if complexity > 10:  # Threshold for complex functions
                hotspots.append({
                    "function": node.name,
                    "complexity": complexity,
                    "line": node.lineno,
                    "issue": "High cyclomatic complexity"
                })

    return hotspots

def _calculate_cyclomatic_complexity(node: ast.AST) -> int:
    """Calculate cyclomatic complexity for Python AST node."""
    complexity = 1  # Base complexity

    for child in ast.walk(node):
        if isinstance(child, (ast.If, ast.While, ast.For, ast.Try, ast.With)):
            complexity += 1
        elif isinstance(child, (ast.And, ast.Or)):
            complexity += 1
        elif isinstance(child, ast.ExceptHandler):
            complexity += 1

    return complexity

async def _analyze_js_ts_structure(content: str) -> Dict[str, Any]:
    """JavaScript/TypeScript structure analysis."""
    structure = {
        "functions": [],
        "classes": [],
        "imports": [],
        "exports": []
    }

    # Function declarations
    func_pattern = r'(?:async\s+)?(?:function\s+(\w+)|const\s+(\w+)\s*=\s*(?:async\s+)?\([^)]*\)\s*=>)'
    functions = re.finditer(func_pattern, content)
    for match in functions:
        name = match.group(1) or match.group(2)
        structure["functions"].append({
            "name": name,
            "type": "async" if "async" in match.group(0) else "sync",
            "style": "declaration" if match.group(1) else "arrow"
        })

    # Class declarations
    class_pattern = r'class\s+(\w+)(?:\s+extends\s+(\w+))?'
    classes = re.finditer(class_pattern, content)
    for match in classes:
        structure["classes"].append({
            "name": match.group(1),
            "extends": match.group(2)
        })

    return structure

async def _analyze_rust_structure(content: str) -> Dict[str, Any]:
    """Rust-specific structure analysis."""
    structure = {
        "structs": [],
        "enums": [],
        "functions": [],
        "traits": [],
        "impls": []
    }

    # Struct definitions
    struct_pattern = r'struct\s+(\w+)'
    structs = re.finditer(struct_pattern, content)
    for match in structs:
        structure["structs"].append({"name": match.group(1)})

    # Function definitions
    fn_pattern = r'(?:pub\s+)?(?:async\s+)?fn\s+(\w+)'
    functions = re.finditer(fn_pattern, content)
    for match in functions:
        structure["functions"].append({
            "name": match.group(1),
            "visibility": "public" if "pub" in match.group(0) else "private",
            "async": "async" in match.group(0)
        })

    return structure

async def _analyze_go_structure(content: str) -> Dict[str, Any]:
    """Go-specific structure analysis."""
    structure = {
        "functions": [],
        "structs": [],
        "interfaces": [],
        "packages": []
    }

    # Function definitions
    func_pattern = r'func\s+(?:\(\w+\s+\*?\w+\)\s+)?(\w+)\s*\('
    functions = re.finditer(func_pattern, content)
    for match in functions:
        structure["functions"].append({"name": match.group(1)})

    # Struct definitions
    struct_pattern = r'type\s+(\w+)\s+struct'
    structs = re.finditer(struct_pattern, content)
    for match in structs:
        structure["structs"].append({"name": match.group(1)})

    return structure

async def _analyze_generic_structure(content: str) -> Dict[str, Any]:
    """Generic structure analysis for unknown languages."""
    lines = content.splitlines()

    return {
        "total_lines": len(lines),
        "blank_lines": len([line for line in lines if not line.strip()]),
        "comment_lines": len([line for line in lines if line.strip().startswith(('#', '//', '/*'))]),
        "code_lines": len([line for line in lines if line.strip() and not line.strip().startswith(('#', '//', '/*'))])
    }

async def _calculate_complexity(content: str, language: str) -> Dict[str, Any]:
    """Calculate various complexity metrics."""
    lines = content.splitlines()

    return {
        "cyclomatic_complexity": await _estimate_cyclomatic_complexity(content, language),
        "nesting_depth": _calculate_max_nesting_depth(content),
        "line_complexity": len([line for line in lines if len(line.strip()) > 80]),
        "function_length": await _analyze_function_lengths(content, language)
    }

async def _estimate_cyclomatic_complexity(content: str, language: str) -> int:
    """Estimate cyclomatic complexity across languages."""
    # Pattern-based complexity estimation
    complexity_patterns = [
        r'\bif\b', r'\bwhile\b', r'\bfor\b', r'\btry\b', r'\bcatch\b',
        r'\bswitch\b', r'\bcase\b', r'\band\b', r'\bor\b', r'\|\|', r'\&\&'
    ]

    complexity = 1  # Base complexity
    for pattern in complexity_patterns:
        matches = re.findall(pattern, content, re.IGNORECASE)
        complexity += len(matches)

    return complexity

def _calculate_max_nesting_depth(content: str) -> int:
    """Calculate maximum nesting depth."""
    max_depth = 0
    current_depth = 0

    for line in content.splitlines():
        stripped = line.strip()
        if not stripped:
            continue

        # Count opening braces
        current_depth += line.count('{') - line.count('}')
        max_depth = max(max_depth, current_depth)

    return max_depth

async def _analyze_function_lengths(content: str, language: str) -> Dict[str, Any]:
    """Analyze function lengths to identify complexity."""
    if language == "python":
        return await _analyze_python_function_lengths(content)
    else:
        # Generic line-based analysis
        return {"average_function_length": "unknown", "long_functions": []}

async def _analyze_python_function_lengths(content: str) -> Dict[str, Any]:
    """Analyze Python function lengths."""
    try:
        tree = ast.parse(content)
        function_lengths = []
        long_functions = []

        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                # Calculate function length (end - start)
                end_line = node.end_lineno or node.lineno
                length = end_line - node.lineno
                function_lengths.append(length)

                if length > 20:  # Threshold for long functions
                    long_functions.append({
                        "name": node.name,
                        "length": length,
                        "line": node.lineno
                    })

        return {
            "average_function_length": sum(function_lengths) / len(function_lengths) if function_lengths else 0,
            "long_functions": long_functions
        }
    except:
        return {"average_function_length": 0, "long_functions": []}

async def _analyze_test_coverage(file_path: str, content: str, language: str) -> Dict[str, Any]:
    """Analyze test coverage and TDD compliance."""
    test_indicators = {
        "has_tests": False,
        "test_patterns": [],
        "assertions_count": 0,
        "mock_usage": False,
        "tdd_compliance": "unknown"
    }

    # Check if this is a test file
    path = Path(file_path)
    is_test_file = any(pattern in path.name.lower() for pattern in ['test', 'spec', '_test.py', '.test.js'])

    if is_test_file:
        test_indicators["has_tests"] = True

        # Count assertions based on language
        if language == "python":
            assertions = re.findall(r'\bassert\b', content)
            test_indicators["assertions_count"] = len(assertions)
            test_indicators["mock_usage"] = "mock" in content.lower()
        elif language in ["javascript", "typescript"]:
            assertions = re.findall(r'\bexpect\b|\bassert\b|\bshould\b', content)
            test_indicators["assertions_count"] = len(assertions)

    return test_indicators

async def _detect_code_smells(content: str, language: str) -> List[Dict[str, Any]]:
    """Detect code smells and anti-patterns."""
    smells = []

    # Long parameter lists
    long_param_pattern = r'def\s+\w+\s*\([^)]{50,}\)'  # Python example
    if re.search(long_param_pattern, content):
        smells.append({
            "type": "long_parameter_list",
            "severity": "medium",
            "description": "Function has too many parameters"
        })

    # Magic numbers
    magic_numbers = re.findall(r'\b(?<![\w.])\d{2,}\b(?![\w.])', content)
    if magic_numbers:
        smells.append({
            "type": "magic_numbers",
            "severity": "low",
            "description": f"Magic numbers detected: {magic_numbers[:5]}"
        })

    # Long methods (generic detection)
    lines = content.splitlines()
    if any(len(line) > 120 for line in lines):
        smells.append({
            "type": "long_lines",
            "severity": "low",
            "description": "Lines exceed recommended length"
        })

    return smells

async def _identify_complexity_issues(content: str, language: str) -> List[Dict[str, Any]]:
    """Identify KISS principle violations."""
    issues = []

    # Nested conditions (KISS violation)
    nesting_depth = _calculate_max_nesting_depth(content)
    if nesting_depth > 4:
        issues.append({
            "type": "deep_nesting",
            "severity": "high",
            "description": f"Maximum nesting depth: {nesting_depth} (exceeds 4)"
        })

    # Complex expressions
    complex_expressions = re.findall(r'[^=\n]{80,}', content)
    if complex_expressions:
        issues.append({
            "type": "complex_expressions",
            "severity": "medium",
            "description": f"Found {len(complex_expressions)} overly complex expressions"
        })

    return issues

async def _analyze_dependencies(content: str, language: str) -> Dict[str, Any]:
    """Analyze dependencies and coupling."""
    if language == "python":
        imports = re.findall(r'(?:from\s+(\S+)\s+)?import\s+([^\n]+)', content)
        return {
            "import_count": len(imports),
            "external_deps": [imp for imp in imports if not imp[0] or not imp[0].startswith('.')],
            "internal_deps": [imp for imp in imports if imp[0] and imp[0].startswith('.')]
        }

    return {"dependencies": "analysis_not_implemented"}

async def _identify_abstractions(content: str, language: str) -> List[Dict[str, Any]]:
    """Identify abstraction patterns and opportunities."""
    abstractions = []

    # Look for repeated patterns that could be abstracted
    lines = content.splitlines()
    line_patterns = {}

    for line in lines:
        # Normalize line (remove specific identifiers)
        normalized = re.sub(r'\b\w+\b', 'VAR', line.strip())
        if len(normalized) > 10:  # Ignore trivial lines
            line_patterns[normalized] = line_patterns.get(normalized, 0) + 1

    # Find patterns that repeat
    for pattern, count in line_patterns.items():
        if count >= 3:  # Repeated 3+ times
            abstractions.append({
                "pattern": pattern,
                "occurrences": count,
                "suggestion": "Consider extracting common pattern"
            })

    return abstractions

async def _score_quality_indicators(analysis: Dict[str, Any]) -> Dict[str, int]:
    """Score quality indicators (0-100 scale)."""
    scores = {}

    # Complexity score (lower complexity = higher score)
    complexity = analysis.get("complexity", {})
    cyclo_complexity = complexity.get("cyclomatic_complexity", 0)
    complexity_score = max(0, 100 - (cyclo_complexity * 5))
    scores["complexity"] = min(100, complexity_score)

    # Structure score
    structure = analysis.get("structure", {})
    if isinstance(structure, dict) and "functions" in structure:
        func_count = len(structure["functions"])
        # Penalize files with too many or too few functions
        if 1 <= func_count <= 10:
            scores["structure"] = 90
        elif func_count == 0:
            scores["structure"] = 50  # Might be data file
        else:
            scores["structure"] = max(50, 90 - (func_count - 10) * 5)
    else:
        scores["structure"] = 70

    # Test coverage score
    test_coverage = analysis.get("test_coverage", {})
    if test_coverage.get("has_tests"):
        scores["testing"] = 85
    else:
        scores["testing"] = 20

    # Code smells penalty
    smells_count = len(analysis.get("smells", []))
    scores["cleanliness"] = max(0, 100 - (smells_count * 15))

    return scores

def _detect_language(file_extension: str) -> str:
    """Detect programming language from file extension."""
    extension_map = {
        ".py": "python",
        ".js": "javascript",
        ".ts": "typescript",
        ".rs": "rust",
        ".go": "go",
        ".java": "java",
        ".cpp": "cpp",
        ".c": "c",
        ".rb": "ruby",
        ".php": "php"
    }

    return extension_map.get(file_extension.lower(), "unknown")

async def calculate_complexity_metrics(file_path: str) -> Dict[str, Any]:
    """Calculate comprehensive complexity metrics for a file."""
    analysis = await deep_code_analysis(file_path)
    return analysis.get("complexity", {})

async def detect_code_smells(file_path: str) -> List[Dict[str, Any]]:
    """Detect code smells in a file."""
    analysis = await deep_code_analysis(file_path)
    return analysis.get("smells", [])