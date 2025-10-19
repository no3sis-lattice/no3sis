"""
Framework-Specific TypeScript Tools

Tools for analyzing React, Node.js, Vue, Angular patterns and suggesting
framework-specific best practices and optimizations.
"""

import json
import re
from pathlib import Path
from typing import Dict, Any, List, Optional


async def analyze_react_patterns(file_path: str, component_type: str = "functional") -> Dict[str, Any]:
    """
    Analyze React component patterns and best practices.

    Args:
        file_path: Path to React component file
        component_type: Type of component analysis (functional, class, hooks)

    Returns:
        Dict with React pattern analysis results
    """
    try:
        path = Path(file_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ File not found: {file_path}"
                }],
                "success": False,
                "error": "file_not_found"
            }

        content = path.read_text(encoding='utf-8')

        # Check if it's a React or Svelte file
        is_react_file = _is_react_file(content)
        is_svelte_file = _is_svelte_file(content)

        if not is_react_file and not is_svelte_file:
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ This doesn't appear to be a React or Svelte file: {file_path}"
                }],
                "success": False,
                "error": "not_supported_framework_file"
            }

        if is_svelte_file:
            analysis = await _analyze_svelte_component(content, str(path), component_type)
        else:
            analysis = await _analyze_react_component(content, str(path), component_type)

        if is_svelte_file:
            formatted_output = _format_svelte_analysis(analysis)
        else:
            formatted_output = _format_react_analysis(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ React analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def analyze_node_patterns(file_path: str, pattern_type: str = "api") -> Dict[str, Any]:
    """
    Analyze Node.js patterns and backend best practices.

    Args:
        file_path: Path to Node.js file
        pattern_type: Type of pattern analysis (api, middleware, server, database)

    Returns:
        Dict with Node.js pattern analysis results
    """
    try:
        path = Path(file_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ File not found: {file_path}"
                }],
                "success": False,
                "error": "file_not_found"
            }

        content = path.read_text(encoding='utf-8')

        # Check if it's a Node.js file
        is_node_file = _is_node_file(content)
        if not is_node_file:
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ This doesn't appear to be a Node.js file: {file_path}"
                }],
                "success": False,
                "error": "not_node_file"
            }

        analysis = await _analyze_node_code(content, str(path), pattern_type)

        formatted_output = _format_node_analysis(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Node.js analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_state_management(project_path: str, framework: str = "react") -> Dict[str, Any]:
    """
    Suggest optimal state management patterns for the project.

    Args:
        project_path: Path to project directory
        framework: Target framework (react, vue, angular)

    Returns:
        Dict with state management recommendations
    """
    try:
        path = Path(project_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Project path not found: {project_path}"
                }],
                "success": False,
                "error": "path_not_found"
            }

        analysis = await _analyze_project_state_management(str(path), framework)

        formatted_output = _format_state_management_suggestions(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "project_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ State management analysis failed for {project_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

def _is_react_file(content: str) -> bool:
    """Check if file contains React code."""
    react_indicators = [
        r"import.*react",
        r"from\s+['\"]react['\"]",
        r"export\s+default\s+function\s+\w+\s*\(",
        r"const\s+\w+\s*=\s*\([^)]*\)\s*=>\s*\(",
        r"<\w+[^>]*>",  # JSX elements
        r"useState|useEffect|useContext",
        r"React\.",
        r"\.tsx?$"
    ]

    return any(re.search(pattern, content, re.IGNORECASE) for pattern in react_indicators)


def _is_svelte_file(content: str) -> bool:
    """Check if file contains Svelte code."""
    svelte_indicators = [
        r"<script[^>]*>",
        r"<style[^>]*>",
        r"\$:",  # Reactive statements
        r"export\s+let\s+\w+",  # Props
        r"import\s+.*from\s+['\"]svelte",
        r"\.svelte$",
        r"onMount|beforeUpdate|afterUpdate",
        r"createEventDispatcher",
        r"\$\w+\s*=",  # Store subscriptions
        r"bind:\w+",
        r"on:\w+"
    ]

    return any(re.search(pattern, content, re.IGNORECASE | re.MULTILINE) for pattern in svelte_indicators)


def _is_node_file(content: str) -> bool:
    """Check if file contains Node.js code."""
    node_indicators = [
        r"require\s*\(['\"]fs['\"]",
        r"require\s*\(['\"]path['\"]",
        r"require\s*\(['\"]express['\"]",
        r"require\s*\(['\"]http['\"]",
        r"import.*express",
        r"process\.env",
        r"__dirname|__filename",
        r"module\.exports|exports\.",
        r"app\.(get|post|put|delete)",
        r"req\.|res\.",
        r"middleware"
    ]

    return any(re.search(pattern, content, re.IGNORECASE) for pattern in node_indicators)


async def _analyze_react_component(content: str, file_path: str, component_type: str) -> Dict[str, Any]:
    """Analyze React component patterns."""

    # Component structure
    component_info = _analyze_component_structure(content)

    # Hook usage
    hooks_analysis = _analyze_react_hooks(content)

    # Props analysis
    props_analysis = _analyze_component_props(content)

    # JSX patterns
    jsx_analysis = _analyze_jsx_patterns(content)

    # Performance patterns
    perf_analysis = _analyze_react_performance(content)

    # Type safety
    type_analysis = _analyze_react_types(content)

    return {
        "component": component_info,
        "hooks": hooks_analysis,
        "props": props_analysis,
        "jsx": jsx_analysis,
        "performance": perf_analysis,
        "types": type_analysis,
        "recommendations": _generate_react_recommendations(
            component_info, hooks_analysis, props_analysis, jsx_analysis
        )
    }


def _analyze_component_structure(content: str) -> Dict[str, Any]:
    """Analyze React component structure."""

    # Functional components
    functional_components = re.findall(
        r'(?:export\s+default\s+)?(?:const|function)\s+(\w+)(?:\s*=\s*)?(?:\([^)]*\))?\s*(?::\s*[^=]+)?\s*(?:=>)?\s*\{',
        content
    )

    # Class components
    class_components = re.findall(
        r'class\s+(\w+)\s+extends\s+(?:React\.)?Component',
        content
    )

    # Component exports
    default_export = bool(re.search(r'export\s+default', content))
    named_exports = len(re.findall(r'export\s+(?:const|function)\s+\w+', content))

    return {
        "functional_components": len(functional_components),
        "class_components": len(class_components),
        "component_names": functional_components + class_components,
        "default_export": default_export,
        "named_exports": named_exports,
        "component_type": "functional" if functional_components else "class" if class_components else "unknown"
    }


def _analyze_react_hooks(content: str) -> Dict[str, Any]:
    """Analyze React hooks usage."""

    hooks = {
        "useState": len(re.findall(r'useState\s*\(', content)),
        "useEffect": len(re.findall(r'useEffect\s*\(', content)),
        "useContext": len(re.findall(r'useContext\s*\(', content)),
        "useReducer": len(re.findall(r'useReducer\s*\(', content)),
        "useMemo": len(re.findall(r'useMemo\s*\(', content)),
        "useCallback": len(re.findall(r'useCallback\s*\(', content)),
        "useRef": len(re.findall(r'useRef\s*\(', content)),
        "useImperativeHandle": len(re.findall(r'useImperativeHandle\s*\(', content)),
        "useLayoutEffect": len(re.findall(r'useLayoutEffect\s*\(', content))
    }

    # Custom hooks
    custom_hooks = re.findall(r'const\s+(use\w+)\s*=', content)

    # Hook rules violations
    violations = []

    # Check for hooks in conditionals (simplified)
    if re.search(r'if\s*\([^)]+\)\s*\{[^}]*use\w+', content):
        violations.append("Hooks may be called inside conditionals")

    return {
        "builtin_hooks": hooks,
        "custom_hooks": custom_hooks,
        "total_hook_calls": sum(hooks.values()),
        "violations": violations,
        "performance_hooks": hooks["useMemo"] + hooks["useCallback"]
    }


def _analyze_component_props(content: str) -> Dict[str, Any]:
    """Analyze component props patterns."""

    # Props interface definitions
    props_interfaces = re.findall(r'interface\s+(\w*Props?)\s*\{', content)

    # Props type definitions
    props_types = re.findall(r'type\s+(\w*Props?)\s*=', content)

    # Optional props
    optional_props = len(re.findall(r'\w+\?\s*:', content))

    # Default props
    default_props = bool(re.search(r'defaultProps|default\s*=', content))

    # Destructuring patterns
    destructuring = bool(re.search(r'\{\s*\w+(?:\s*,\s*\w+)*\s*\}', content))

    return {
        "props_interfaces": props_interfaces,
        "props_types": props_types,
        "total_prop_definitions": len(props_interfaces) + len(props_types),
        "optional_props": optional_props,
        "has_default_props": default_props,
        "uses_destructuring": destructuring
    }


def _analyze_jsx_patterns(content: str) -> Dict[str, Any]:
    """Analyze JSX usage patterns."""

    # JSX elements
    jsx_elements = len(re.findall(r'<\w+[^>]*>', content))

    # Conditional rendering
    conditional_rendering = len(re.findall(r'\w+\s*&&\s*<', content)) + len(re.findall(r'\?\s*<[^>]+>\s*:\s*<', content))

    # Map operations
    map_operations = len(re.findall(r'\.map\s*\([^)]*=>\s*<', content))

    # Event handlers
    event_handlers = len(re.findall(r'on\w+\s*=\s*\{', content))

    # Inline styles
    inline_styles = len(re.findall(r'style\s*=\s*\{\{', content))

    # Class names
    class_names = len(re.findall(r'className\s*=', content))

    return {
        "jsx_elements": jsx_elements,
        "conditional_rendering": conditional_rendering,
        "map_operations": map_operations,
        "event_handlers": event_handlers,
        "inline_styles": inline_styles,
        "class_names": class_names
    }


def _analyze_react_performance(content: str) -> Dict[str, Any]:
    """Analyze React performance patterns."""

    # Memoization
    memo_usage = bool(re.search(r'React\.memo|memo\s*\(', content))
    use_memo = len(re.findall(r'useMemo\s*\(', content))
    use_callback = len(re.findall(r'useCallback\s*\(', content))

    # Lazy loading
    lazy_components = len(re.findall(r'React\.lazy|lazy\s*\(', content))
    suspense = bool(re.search(r'<Suspense', content))

    # Performance anti-patterns
    anti_patterns = []

    # Inline object/function creation in JSX
    if re.search(r'=\s*\{\s*\{', content):
        anti_patterns.append("Inline object creation in JSX")

    if re.search(r'=\s*\{\s*\([^)]*\)\s*=>', content):
        anti_patterns.append("Inline function creation in JSX")

    # Large useEffect dependencies
    large_deps = len(re.findall(r'useEffect\s*\([^,]*,\s*\[[^\]]{50,}\]', content))
    if large_deps > 0:
        anti_patterns.append(f"Large useEffect dependency arrays ({large_deps})")

    return {
        "memo_usage": memo_usage,
        "use_memo_calls": use_memo,
        "use_callback_calls": use_callback,
        "lazy_components": lazy_components,
        "suspense_usage": suspense,
        "anti_patterns": anti_patterns,
        "performance_score": _calculate_react_performance_score(
            memo_usage, use_memo, use_callback, len(anti_patterns)
        )
    }


def _analyze_react_types(content: str) -> Dict[str, Any]:
    """Analyze React TypeScript patterns."""

    # Component typing
    fc_typing = bool(re.search(r':\s*(?:React\.)?FC(?:<[^>]+>)?', content))

    # Event typing
    event_types = len(re.findall(r':\s*(?:React\.)?(?:Mouse|Change|Form|Key)Event', content))

    # Ref typing
    ref_types = len(re.findall(r'useRef<[^>]+>', content))

    # Props typing
    generic_props = bool(re.search(r'<Props>', content))

    return {
        "uses_fc_type": fc_typing,
        "event_types": event_types,
        "typed_refs": ref_types,
        "generic_props": generic_props
    }


async def _analyze_svelte_component(content: str, file_path: str, component_type: str) -> Dict[str, Any]:
    """Analyze Svelte component patterns."""

    # Component structure
    component_info = _analyze_svelte_structure(content)

    # Reactivity analysis
    reactivity_analysis = _analyze_svelte_reactivity(content)

    # Props and stores
    props_stores_analysis = _analyze_svelte_props_stores(content)

    # Lifecycle and events
    lifecycle_analysis = _analyze_svelte_lifecycle(content)

    # Performance patterns
    perf_analysis = _analyze_svelte_performance(content)

    # Type safety (if TypeScript)
    type_analysis = _analyze_svelte_types(content, file_path)

    return {
        "framework": "svelte",
        "component": component_info,
        "reactivity": reactivity_analysis,
        "props_stores": props_stores_analysis,
        "lifecycle": lifecycle_analysis,
        "performance": perf_analysis,
        "types": type_analysis,
        "recommendations": _generate_svelte_recommendations(
            component_info, reactivity_analysis, props_stores_analysis, perf_analysis
        )
    }


def _analyze_svelte_structure(content: str) -> Dict[str, Any]:
    """Analyze Svelte component structure."""

    # Script blocks
    script_blocks = len(re.findall(r'<script[^>]*>', content))
    typescript_script = bool(re.search(r'<script[^>]*lang=["\']ts["\']', content))

    # Style blocks
    style_blocks = len(re.findall(r'<style[^>]*>', content))
    scoped_styles = bool(re.search(r'<style[^>]*scoped[^>]*>', content))

    # Component exports (props)
    exported_props = len(re.findall(r'export\s+let\s+\w+', content))

    # Template structure
    template_complexity = _analyze_svelte_template(content)

    return {
        "script_blocks": script_blocks,
        "typescript": typescript_script,
        "style_blocks": style_blocks,
        "scoped_styles": scoped_styles,
        "exported_props": exported_props,
        "template": template_complexity,
        "component_type": "single-file" if script_blocks > 0 else "template-only"
    }


def _analyze_svelte_template(content: str) -> Dict[str, Any]:
    """Analyze Svelte template complexity."""

    # Remove script and style blocks for template analysis
    template_content = re.sub(r'<script[^>]*>.*?</script>', '', content, flags=re.DOTALL)
    template_content = re.sub(r'<style[^>]*>.*?</style>', '', template_content, flags=re.DOTALL)

    return {
        "elements": len(re.findall(r'<\w+[^>]*/?>', template_content)),
        "conditionals": len(re.findall(r'\{#if\b', template_content)),
        "loops": len(re.findall(r'\{#each\b', template_content)),
        "await_blocks": len(re.findall(r'\{#await\b', template_content)),
        "slots": len(re.findall(r'<slot[^>]*/?>', template_content)),
        "components": len(re.findall(r'<[A-Z]\w+[^>]*/?>', template_content))
    }


def _analyze_svelte_reactivity(content: str) -> Dict[str, Any]:
    """Analyze Svelte reactivity patterns."""

    # Reactive statements
    reactive_statements = len(re.findall(r'\$:\s*\w+', content))

    # Reactive declarations
    reactive_declarations = len(re.findall(r'\$:\s*\w+\s*=', content))

    # Store subscriptions
    store_subscriptions = len(re.findall(r'\$\w+', content))

    # Complex reactive statements
    complex_reactive = len(re.findall(r'\$:\s*\{', content))

    return {
        "reactive_statements": reactive_statements,
        "reactive_declarations": reactive_declarations,
        "store_subscriptions": store_subscriptions,
        "complex_reactive": complex_reactive,
        "total_reactivity": reactive_statements + reactive_declarations + store_subscriptions
    }


def _analyze_svelte_props_stores(content: str) -> Dict[str, Any]:
    """Analyze props and store usage."""

    # Props (exported let)
    props = re.findall(r'export\s+let\s+(\w+)(?:\s*=\s*[^;]+)?', content)

    # Store imports
    store_imports = len(re.findall(r'import\s+.*from\s+["\']svelte/store["\']', content))

    # Store creations
    writable_stores = len(re.findall(r'writable\s*\(', content))
    readable_stores = len(re.findall(r'readable\s*\(', content))
    derived_stores = len(re.findall(r'derived\s*\(', content))

    # Context usage
    context_set = len(re.findall(r'setContext\s*\(', content))
    context_get = len(re.findall(r'getContext\s*\(', content))

    return {
        "props": {
            "count": len(props),
            "names": props[:10]  # Limit to first 10
        },
        "stores": {
            "imports": store_imports,
            "writable": writable_stores,
            "readable": readable_stores,
            "derived": derived_stores
        },
        "context": {
            "set": context_set,
            "get": context_get
        }
    }


def _analyze_svelte_lifecycle(content: str) -> Dict[str, Any]:
    """Analyze lifecycle and event patterns."""

    # Lifecycle functions
    lifecycle = {
        "onMount": len(re.findall(r'onMount\s*\(', content)),
        "beforeUpdate": len(re.findall(r'beforeUpdate\s*\(', content)),
        "afterUpdate": len(re.findall(r'afterUpdate\s*\(', content)),
        "onDestroy": len(re.findall(r'onDestroy\s*\(', content))
    }

    # Event handling
    event_handlers = len(re.findall(r'on:\w+\s*=', content))
    custom_events = len(re.findall(r'createEventDispatcher\s*\(', content))

    # Bindings
    bindings = {
        "value": len(re.findall(r'bind:value', content)),
        "checked": len(re.findall(r'bind:checked', content)),
        "this": len(re.findall(r'bind:this', content)),
        "other": len(re.findall(r'bind:\w+', content)) - len(re.findall(r'bind:(?:value|checked|this)', content))
    }

    return {
        "lifecycle": lifecycle,
        "events": {
            "handlers": event_handlers,
            "custom": custom_events
        },
        "bindings": bindings
    }


def _analyze_svelte_performance(content: str) -> Dict[str, Any]:
    """Analyze Svelte performance patterns."""

    # Performance considerations
    anti_patterns = []

    # Large reactive statements
    reactive_statements = re.findall(r'\$:.*', content)
    complex_reactive = [stmt for stmt in reactive_statements if len(stmt) > 100]
    if complex_reactive:
        anti_patterns.append(f"Complex reactive statements: {len(complex_reactive)}")

    # Too many store subscriptions in template
    template_subscriptions = len(re.findall(r'\{\$\w+', content))
    if template_subscriptions > 10:
        anti_patterns.append(f"Many store subscriptions in template: {template_subscriptions}")

    # Inline functions in template
    inline_functions = len(re.findall(r'on:\w+\s*=\s*\{[^}]*=>', content))
    if inline_functions > 3:
        anti_patterns.append(f"Inline arrow functions in template: {inline_functions}")

    # Performance optimizations
    optimizations = []
    if 'use:' in content:
        optimizations.append("Uses actions for DOM manipulation")
    if '{@const ' in content:
        optimizations.append("Uses template constants")

    return {
        "anti_patterns": anti_patterns,
        "optimizations": optimizations,
        "performance_score": _calculate_svelte_performance_score(len(anti_patterns), len(optimizations))
    }


def _analyze_svelte_types(content: str, file_path: str) -> Dict[str, Any]:
    """Analyze Svelte TypeScript patterns."""

    is_typescript = file_path.endswith('.ts') or 'lang="ts"' in content or "lang='ts'" in content

    if not is_typescript:
        return {"typescript": False}

    # Type annotations for props
    typed_props = len(re.findall(r'export\s+let\s+\w+\s*:\s*\w+', content))

    # Interface definitions
    interfaces = len(re.findall(r'interface\s+\w+', content))

    # Generic components
    generics = len(re.findall(r'<script[^>]*generics\s*=', content))

    # Type assertions
    assertions = len(re.findall(r'as\s+\w+', content))

    return {
        "typescript": True,
        "typed_props": typed_props,
        "interfaces": interfaces,
        "generics": generics,
        "type_assertions": assertions,
        "type_safety_score": _calculate_svelte_type_score(typed_props, interfaces, assertions)
    }


def _generate_svelte_recommendations(component_info: Dict, reactivity_info: Dict,
                                   props_stores_info: Dict, perf_info: Dict) -> List[Dict[str, Any]]:
    """Generate Svelte-specific recommendations."""
    recommendations = []

    # TypeScript recommendation
    if not component_info.get("typescript", False):
        recommendations.append({
            "type": "typescript",
            "priority": "medium",
            "message": "Consider using TypeScript for better type safety",
            "benefit": "Better developer experience and error catching",
            "example": '<script lang="ts">'
        })

    # Scoped styles recommendation
    if component_info.get("style_blocks", 0) > 0 and not component_info.get("scoped_styles", False):
        recommendations.append({
            "type": "scoped_styles",
            "priority": "low",
            "message": "Consider using scoped styles to prevent CSS conflicts",
            "benefit": "Prevents style leaking between components",
            "example": '<style scoped>'
        })

    # Performance recommendations
    anti_patterns = perf_info.get("anti_patterns", [])
    if anti_patterns:
        recommendations.append({
            "type": "performance",
            "priority": "medium",
            "message": f"Performance issues found: {len(anti_patterns)}",
            "issues": anti_patterns[:3],
            "benefit": "Better runtime performance and user experience"
        })

    # Reactivity recommendations
    if reactivity_info.get("total_reactivity", 0) == 0 and component_info.get("exported_props", 0) > 0:
        recommendations.append({
            "type": "reactivity",
            "priority": "low",
            "message": "Component has props but no reactive statements",
            "suggestion": "Consider adding reactive statements if derived state is needed",
            "example": "$: computedValue = prop1 + prop2"
        })

    return recommendations


def _calculate_svelte_performance_score(anti_patterns_count: int, optimizations_count: int) -> int:
    """Calculate Svelte performance score."""
    score = 100
    score -= anti_patterns_count * 15  # Penalty for anti-patterns
    score += min(optimizations_count * 10, 30)  # Bonus for optimizations
    return max(0, min(100, score))


def _calculate_svelte_type_score(typed_props: int, interfaces: int, assertions: int) -> int:
    """Calculate Svelte TypeScript usage score."""
    score = 50  # Base score for using TypeScript
    score += min(typed_props * 10, 30)  # Bonus for typed props
    score += min(interfaces * 5, 20)    # Bonus for interfaces
    score -= min(assertions * 5, 20)    # Penalty for type assertions
    return max(0, min(100, score))


def _format_svelte_analysis(analysis: Dict[str, Any]) -> str:
    """Format Svelte analysis results."""
    output = []

    output.append("⚡ **Svelte Component Analysis**\n")

    # Component info
    component = analysis.get("component", {})
    comp_type = component.get("component_type", "unknown")
    output.append(f"📱 **Component Type:** {comp_type}")
    output.append(f"- Script blocks: {component.get('script_blocks', 0)}")
    output.append(f"- TypeScript: {'✅' if component.get('typescript') else '❌'}")
    output.append(f"- Style blocks: {component.get('style_blocks', 0)}")
    output.append(f"- Scoped styles: {'✅' if component.get('scoped_styles') else '❌'}")
    output.append(f"- Props: {component.get('exported_props', 0)}")
    output.append("")

    # Template complexity
    template = component.get("template", {})
    if template:
        output.append("🏗️ **Template Structure:**")
        output.append(f"- Elements: {template.get('elements', 0)}")
        output.append(f"- Conditionals: {template.get('conditionals', 0)}")
        output.append(f"- Loops: {template.get('loops', 0)}")
        output.append(f"- Components: {template.get('components', 0)}")
        if template.get('slots', 0) > 0:
            output.append(f"- Slots: {template['slots']}")
        output.append("")

    # Reactivity analysis
    reactivity = analysis.get("reactivity", {})
    if reactivity.get("total_reactivity", 0) > 0:
        output.append("🔄 **Reactivity:**")
        output.append(f"- Reactive statements: {reactivity.get('reactive_statements', 0)}")
        output.append(f"- Reactive declarations: {reactivity.get('reactive_declarations', 0)}")
        output.append(f"- Store subscriptions: {reactivity.get('store_subscriptions', 0)}")
        output.append("")

    # Stores and props
    props_stores = analysis.get("props_stores", {})
    stores = props_stores.get("stores", {})
    if stores.get("imports", 0) > 0 or any(stores.values()):
        output.append("🏪 **Stores:**")
        if stores.get("writable", 0) > 0:
            output.append(f"- Writable stores: {stores['writable']}")
        if stores.get("readable", 0) > 0:
            output.append(f"- Readable stores: {stores['readable']}")
        if stores.get("derived", 0) > 0:
            output.append(f"- Derived stores: {stores['derived']}")
        output.append("")

    # Lifecycle and events
    lifecycle = analysis.get("lifecycle", {})
    lifecycle_funcs = lifecycle.get("lifecycle", {})
    if any(lifecycle_funcs.values()):
        output.append("🔄 **Lifecycle:**")
        for func, count in lifecycle_funcs.items():
            if count > 0:
                output.append(f"- {func}: {count}")

        events = lifecycle.get("events", {})
        output.append(f"- Event handlers: {events.get('handlers', 0)}")
        output.append(f"- Custom events: {events.get('custom', 0)}")
        output.append("")

    # Performance analysis
    perf = analysis.get("performance", {})
    if perf:
        score = perf.get("performance_score", 0)
        score_emoji = "🟢" if score >= 80 else "🟡" if score >= 60 else "🔴"
        output.append(f"{score_emoji} **Performance Score: {score}/100**")

        anti_patterns = perf.get("anti_patterns", [])
        if anti_patterns:
            output.append("⚠️ Performance issues:")
            for pattern in anti_patterns:
                output.append(f"  - {pattern}")

        optimizations = perf.get("optimizations", [])
        if optimizations:
            output.append("✅ Optimizations found:")
            for opt in optimizations:
                output.append(f"  - {opt}")
        output.append("")

    # TypeScript analysis
    types = analysis.get("types", {})
    if types.get("typescript", False):
        output.append("🔷 **TypeScript Usage:**")
        output.append(f"- Typed props: {types.get('typed_props', 0)}")
        output.append(f"- Interfaces: {types.get('interfaces', 0)}")
        output.append(f"- Type safety score: {types.get('type_safety_score', 0)}/100")
        output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")

            if rec.get("benefit"):
                output.append(f"   ✅ {rec['benefit']}")
            if rec.get("suggestion"):
                output.append(f"   💡 {rec['suggestion']}")
            if rec.get("example"):
                output.append(f"   📝 Example: `{rec['example']}`")
            if rec.get("issues"):
                for issue in rec["issues"]:
                    output.append(f"   - {issue}")
        output.append("")

    return '\n'.join(output)


async def _analyze_node_code(content: str, file_path: str, pattern_type: str) -> Dict[str, Any]:
    """Analyze Node.js code patterns."""

    # Express patterns
    express_analysis = _analyze_express_patterns(content)

    # Async patterns
    async_analysis = _analyze_async_patterns(content)

    # Error handling
    error_analysis = _analyze_error_handling(content)

    # Security patterns
    security_analysis = _analyze_security_patterns(content)

    # Performance patterns
    performance_analysis = _analyze_node_performance(content)

    return {
        "express": express_analysis,
        "async": async_analysis,
        "error_handling": error_analysis,
        "security": security_analysis,
        "performance": performance_analysis,
        "recommendations": _generate_node_recommendations(
            express_analysis, async_analysis, error_analysis, security_analysis
        )
    }


def _analyze_express_patterns(content: str) -> Dict[str, Any]:
    """Analyze Express.js patterns."""

    # Route definitions
    routes = {
        "get": len(re.findall(r'\.get\s*\(', content)),
        "post": len(re.findall(r'\.post\s*\(', content)),
        "put": len(re.findall(r'\.put\s*\(', content)),
        "delete": len(re.findall(r'\.delete\s*\(', content)),
        "patch": len(re.findall(r'\.patch\s*\(', content))
    }

    # Middleware usage
    middleware = {
        "use": len(re.findall(r'\.use\s*\(', content)),
        "custom": len(re.findall(r'function\s+\w+\s*\(\s*req\s*,\s*res\s*,\s*next\s*\)', content))
    }

    # Request/Response patterns
    req_patterns = len(re.findall(r'req\.\w+', content))
    res_patterns = len(re.findall(r'res\.\w+', content))

    return {
        "routes": routes,
        "total_routes": sum(routes.values()),
        "middleware": middleware,
        "req_patterns": req_patterns,
        "res_patterns": res_patterns,
        "uses_express": sum(routes.values()) > 0 or middleware["use"] > 0
    }


def _analyze_async_patterns(content: str) -> Dict[str, Any]:
    """Analyze async/await patterns."""

    # Async functions
    async_functions = len(re.findall(r'async\s+function|\w+\s*=\s*async', content))

    # Await usage
    await_calls = len(re.findall(r'await\s+', content))

    # Promise patterns
    promise_chains = len(re.findall(r'\.then\s*\(', content))
    promise_catches = len(re.findall(r'\.catch\s*\(', content))

    # Promise creation
    new_promises = len(re.findall(r'new\s+Promise\s*\(', content))

    return {
        "async_functions": async_functions,
        "await_calls": await_calls,
        "promise_chains": promise_chains,
        "promise_catches": promise_catches,
        "new_promises": new_promises,
        "prefers_async_await": await_calls > promise_chains
    }


def _analyze_error_handling(content: str) -> Dict[str, Any]:
    """Analyze error handling patterns."""

    # Try-catch blocks
    try_catch = len(re.findall(r'try\s*\{', content))

    # Error middleware
    error_middleware = len(re.findall(r'function\s*\([^)]*err[^)]*,\s*req\s*,\s*res\s*,\s*next\s*\)', content))

    # Error throwing
    throw_statements = len(re.findall(r'throw\s+', content))

    # Error classes
    error_classes = len(re.findall(r'class\s+\w*Error', content))

    # Unhandled promise rejections
    unhandled_check = bool(re.search(r'unhandledRejection', content))

    return {
        "try_catch_blocks": try_catch,
        "error_middleware": error_middleware,
        "throw_statements": throw_statements,
        "custom_error_classes": error_classes,
        "handles_unhandled_rejections": unhandled_check
    }


def _analyze_security_patterns(content: str) -> Dict[str, Any]:
    """Analyze security patterns."""

    # Input validation
    validation_libs = bool(re.search(r'joi|yup|express-validator', content))

    # Authentication
    auth_patterns = bool(re.search(r'passport|jwt|bcrypt', content))

    # Environment variables
    env_usage = len(re.findall(r'process\.env\.\w+', content))

    # CORS
    cors_usage = bool(re.search(r'cors', content))

    # Helmet usage
    helmet_usage = bool(re.search(r'helmet', content))

    # Security issues
    security_issues = []

    if re.search(r'exec\s*\(', content):
        security_issues.append("Direct shell command execution detected")

    if re.search(r'innerHTML\s*=', content):
        security_issues.append("Potential XSS vulnerability with innerHTML")

    return {
        "input_validation": validation_libs,
        "authentication": auth_patterns,
        "env_variables": env_usage,
        "cors_enabled": cors_usage,
        "helmet_enabled": helmet_usage,
        "security_issues": security_issues
    }


def _analyze_node_performance(content: str) -> Dict[str, Any]:
    """Analyze Node.js performance patterns."""

    # Clustering
    cluster_usage = bool(re.search(r'cluster', content))

    # Caching
    cache_patterns = bool(re.search(r'redis|memcached|cache', content))

    # Streaming
    stream_usage = len(re.findall(r'\.pipe\s*\(|stream', content))

    # Database patterns
    db_connections = bool(re.search(r'mongoose|pool|connection', content))

    return {
        "clustering": cluster_usage,
        "caching": cache_patterns,
        "streaming": stream_usage,
        "database_connections": db_connections
    }


async def _analyze_project_state_management(project_path: str, framework: str) -> Dict[str, Any]:
    """Analyze project-wide state management patterns."""

    path = Path(project_path)

    # Find relevant files
    js_files = list(path.glob('**/*.{js,jsx,ts,tsx}'))[:50]  # Limit to first 50 files

    # Analyze package.json for dependencies
    package_json = path / "package.json"
    dependencies = {}
    if package_json.exists():
        try:
            pkg_data = json.loads(package_json.read_text())
            dependencies = {
                **pkg_data.get("dependencies", {}),
                **pkg_data.get("devDependencies", {})
            }
        except Exception:
            pass

    # State management libraries
    state_libs = _detect_state_libraries(dependencies)

    # Analyze state patterns in code
    state_patterns = _analyze_state_patterns_in_files(js_files, framework)

    # Generate recommendations
    recommendations = _generate_state_management_recommendations(
        state_libs, state_patterns, len(js_files), framework
    )

    return {
        "project_size": len(js_files),
        "dependencies": state_libs,
        "patterns": state_patterns,
        "recommendations": recommendations,
        "framework": framework
    }


def _detect_state_libraries(dependencies: Dict[str, str]) -> Dict[str, Any]:
    """Detect state management libraries in dependencies."""

    state_libs = {
        "redux": "redux" in dependencies,
        "mobx": "mobx" in dependencies,
        "zustand": "zustand" in dependencies,
        "jotai": "jotai" in dependencies,
        "recoil": "recoil" in dependencies,
        "valtio": "valtio" in dependencies,
        "context_api": False,  # Will be detected from code analysis
        "react_query": "@tanstack/react-query" in dependencies or "react-query" in dependencies,
        "swr": "swr" in dependencies,
        "svelte_stores": "svelte" in dependencies,  # Built-in Svelte stores
        "svelte_writable": False,  # Will be detected from code analysis
        "svelte_readable": False,  # Will be detected from code analysis
        "svelte_derived": False   # Will be detected from code analysis
    }

    return state_libs


def _analyze_state_patterns_in_files(files: List[Path], framework: str) -> Dict[str, Any]:
    """Analyze state management patterns across files."""

    patterns = {
        "context_providers": 0,
        "usestate_calls": 0,
        "usereducer_calls": 0,
        "custom_hooks": 0,
        "prop_drilling_depth": 0,
        "state_sharing_files": 0,
        # Svelte-specific patterns
        "svelte_stores": 0,
        "reactive_statements": 0,
        "context_usage": 0
    }

    for file in files:
        try:
            content = file.read_text(encoding='utf-8')

            # Context API usage
            patterns["context_providers"] += len(re.findall(r'createContext|\.Provider', content))

            # Hook usage
            patterns["usestate_calls"] += len(re.findall(r'useState\s*\(', content))
            patterns["usereducer_calls"] += len(re.findall(r'useReducer\s*\(', content))

            # Custom hooks
            patterns["custom_hooks"] += len(re.findall(r'const\s+(use\w+)\s*=', content))

            # Prop drilling detection (simplified)
            prop_depth = len(re.findall(r'props\.\w+(?:\.\w+)+', content))
            patterns["prop_drilling_depth"] = max(patterns["prop_drilling_depth"], prop_depth)

            # Files sharing state
            if any(pattern in content for pattern in ['useState', 'useContext', 'useReducer']):
                patterns["state_sharing_files"] += 1

            # Svelte-specific patterns
            if framework == "svelte" or file.suffix == '.svelte':
                patterns["svelte_stores"] += len(re.findall(r'(writable|readable|derived)\s*\(', content))
                patterns["reactive_statements"] += len(re.findall(r'\$:', content))
                patterns["context_usage"] += len(re.findall(r'(get|set)Context\s*\(', content))

                # Update state sharing files for Svelte
                if any(pattern in content for pattern in ['$:', 'writable', 'readable', 'derived', 'getContext']):
                    patterns["state_sharing_files"] += 1

        except Exception:
            continue

    return patterns


def _generate_react_recommendations(component_info: Dict, hooks_info: Dict,
                                  props_info: Dict, jsx_info: Dict) -> List[Dict[str, Any]]:
    """Generate React-specific recommendations."""
    recommendations = []

    # Component structure recommendations
    if component_info["class_components"] > 0:
        recommendations.append({
            "type": "modernization",
            "priority": "medium",
            "message": "Consider migrating class components to functional components with hooks",
            "benefit": "Better performance and modern React patterns"
        })

    # Hook recommendations
    if hooks_info["total_hook_calls"] > 10 and hooks_info["performance_hooks"] == 0:
        recommendations.append({
            "type": "performance",
            "priority": "high",
            "message": "Consider using useMemo and useCallback for optimization",
            "benefit": "Prevent unnecessary re-renders and improve performance"
        })

    # Props recommendations
    if props_info["total_prop_definitions"] == 0:
        recommendations.append({
            "type": "type_safety",
            "priority": "high",
            "message": "Define TypeScript interfaces for component props",
            "benefit": "Better type safety and developer experience"
        })

    return recommendations


def _generate_node_recommendations(express_info: Dict, async_info: Dict,
                                 error_info: Dict, security_info: Dict) -> List[Dict[str, Any]]:
    """Generate Node.js-specific recommendations."""
    recommendations = []

    # Async recommendations
    if async_info["promise_chains"] > async_info["await_calls"]:
        recommendations.append({
            "type": "modernization",
            "priority": "medium",
            "message": "Consider migrating Promise chains to async/await",
            "benefit": "Better readability and error handling"
        })

    # Error handling recommendations
    if error_info["try_catch_blocks"] == 0 and async_info["async_functions"] > 0:
        recommendations.append({
            "type": "error_handling",
            "priority": "high",
            "message": "Add try-catch blocks for async functions",
            "benefit": "Proper error handling prevents crashes"
        })

    # Security recommendations
    if not security_info["helmet_enabled"] and express_info["uses_express"]:
        recommendations.append({
            "type": "security",
            "priority": "high",
            "message": "Add Helmet middleware for security headers",
            "benefit": "Protection against common web vulnerabilities"
        })

    return recommendations


def _generate_state_management_recommendations(libs: Dict, patterns: Dict,
                                             project_size: int, framework: str) -> List[Dict[str, Any]]:
    """Generate state management recommendations."""
    recommendations = []

    # Project size based recommendations
    if project_size > 20 and not any(libs.values()):
        recommendations.append({
            "type": "state_library",
            "priority": "high",
            "message": "Consider adopting a state management library for large project",
            "suggestions": ["Zustand (lightweight)", "Redux Toolkit (mature)", "Jotai (atomic)"]
        })

    # Context API overuse
    if patterns["context_providers"] > 5:
        recommendations.append({
            "type": "performance",
            "priority": "medium",
            "message": "Multiple Context providers may cause performance issues",
            "suggestion": "Consider consolidating contexts or using a dedicated state library"
        })

    # Prop drilling
    if patterns["prop_drilling_depth"] > 3:
        recommendations.append({
            "type": "architecture",
            "priority": "medium",
            "message": "Deep prop drilling detected",
            "suggestion": "Use Context API or state management library for shared state"
        })

    return recommendations


def _calculate_react_performance_score(memo_usage: bool, use_memo: int,
                                     use_callback: int, anti_patterns: int) -> int:
    """Calculate React performance score."""
    score = 100

    # Penalties for anti-patterns
    score -= anti_patterns * 15

    # Bonus for optimization techniques
    if memo_usage:
        score += 10
    if use_memo > 0:
        score += min(use_memo * 5, 20)
    if use_callback > 0:
        score += min(use_callback * 5, 20)

    return max(0, min(100, score))


def _format_react_analysis(analysis: Dict[str, Any]) -> str:
    """Format React analysis results."""
    output = []

    output.append("⚛️ **React Component Analysis**\n")

    # Component info
    component = analysis.get("component", {})
    comp_type = component.get("component_type", "unknown")
    output.append(f"📱 **Component Type:** {comp_type.title()}")
    output.append(f"- Functional components: {component.get('functional_components', 0)}")
    output.append(f"- Class components: {component.get('class_components', 0)}")
    output.append("")

    # Hooks analysis
    hooks = analysis.get("hooks", {})
    if hooks.get("total_hook_calls", 0) > 0:
        output.append("🪝 **Hooks Usage:**")
        builtin_hooks = hooks.get("builtin_hooks", {})
        for hook, count in builtin_hooks.items():
            if count > 0:
                output.append(f"- {hook}: {count}")

        custom_hooks = hooks.get("custom_hooks", [])
        if custom_hooks:
            output.append(f"- Custom hooks: {', '.join(custom_hooks)}")

        violations = hooks.get("violations", [])
        if violations:
            output.append("⚠️ Hook rule violations:")
            for violation in violations:
                output.append(f"  - {violation}")
        output.append("")

    # Performance analysis
    perf = analysis.get("performance", {})
    if perf:
        score = perf.get("performance_score", 0)
        score_emoji = "🟢" if score >= 80 else "🟡" if score >= 60 else "🔴"
        output.append(f"{score_emoji} **Performance Score: {score}/100**")

        anti_patterns = perf.get("anti_patterns", [])
        if anti_patterns:
            output.append("⚠️ Performance issues:")
            for pattern in anti_patterns:
                output.append(f"  - {pattern}")
        output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("benefit"):
                output.append(f"   ✅ {rec['benefit']}")
        output.append("")

    return '\n'.join(output)


def _format_node_analysis(analysis: Dict[str, Any]) -> str:
    """Format Node.js analysis results."""
    output = []

    output.append("🟢 **Node.js Analysis**\n")

    # Express analysis
    express = analysis.get("express", {})
    if express.get("uses_express", False):
        output.append("🚀 **Express.js Patterns:**")
        routes = express.get("routes", {})
        total_routes = sum(routes.values())
        output.append(f"- Total routes: {total_routes}")
        for method, count in routes.items():
            if count > 0:
                output.append(f"  - {method.upper()}: {count}")

        middleware = express.get("middleware", {})
        output.append(f"- Middleware usage: {middleware.get('use', 0)}")
        output.append("")

    # Async patterns
    async_info = analysis.get("async", {})
    output.append("⚡ **Async Patterns:**")
    output.append(f"- Async functions: {async_info.get('async_functions', 0)}")
    output.append(f"- Await calls: {async_info.get('await_calls', 0)}")
    output.append(f"- Promise chains: {async_info.get('promise_chains', 0)}")

    if async_info.get("prefers_async_await"):
        output.append("✅ Uses modern async/await pattern")
    else:
        output.append("⚠️ Consider migrating to async/await")
    output.append("")

    # Error handling
    error_info = analysis.get("error_handling", {})
    output.append("🛡️ **Error Handling:**")
    output.append(f"- Try-catch blocks: {error_info.get('try_catch_blocks', 0)}")
    output.append(f"- Error middleware: {error_info.get('error_middleware', 0)}")
    output.append(f"- Custom error classes: {error_info.get('custom_error_classes', 0)}")

    if error_info.get("handles_unhandled_rejections"):
        output.append("✅ Handles unhandled promise rejections")
    output.append("")

    # Security
    security = analysis.get("security", {})
    output.append("🔒 **Security Analysis:**")
    output.append(f"- Input validation: {'✅' if security.get('input_validation') else '❌'}")
    output.append(f"- Authentication patterns: {'✅' if security.get('authentication') else '❌'}")
    output.append(f"- CORS enabled: {'✅' if security.get('cors_enabled') else '❌'}")
    output.append(f"- Helmet enabled: {'✅' if security.get('helmet_enabled') else '❌'}")

    issues = security.get("security_issues", [])
    if issues:
        output.append("🚨 Security issues found:")
        for issue in issues:
            output.append(f"  - {issue}")
    output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("benefit"):
                output.append(f"   ✅ {rec['benefit']}")
        output.append("")

    return '\n'.join(output)


def _format_state_management_suggestions(analysis: Dict[str, Any]) -> str:
    """Format state management analysis results."""
    output = []

    framework = analysis.get("framework", "react").title()
    project_size = analysis.get("project_size", 0)

    output.append(f"🎯 **{framework} State Management Analysis**\n")
    output.append(f"📊 **Project Size:** {project_size} files\n")

    # Current state libraries
    libs = analysis.get("dependencies", {})
    active_libs = [lib for lib, active in libs.items() if active]

    if active_libs:
        output.append("📚 **Current State Libraries:**")
        for lib in active_libs:
            output.append(f"- {lib.replace('_', ' ').title()}")
        output.append("")

    # State patterns
    patterns = analysis.get("patterns", {})
    output.append("🔍 **State Patterns:**")
    output.append(f"- useState calls: {patterns.get('usestate_calls', 0)}")
    output.append(f"- Context providers: {patterns.get('context_providers', 0)}")
    output.append(f"- Custom hooks: {patterns.get('custom_hooks', 0)}")
    output.append(f"- Files with state: {patterns.get('state_sharing_files', 0)}")

    if patterns.get("prop_drilling_depth", 0) > 2:
        output.append(f"⚠️ Prop drilling depth: {patterns['prop_drilling_depth']}")
    output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")

            if rec.get("suggestions"):
                output.append("   Options:")
                for suggestion in rec["suggestions"]:
                    output.append(f"   - {suggestion}")
            elif rec.get("suggestion"):
                output.append(f"   💡 {rec['suggestion']}")
        output.append("")
    else:
        output.append("✅ State management looks good for current project size!")

    return '\n'.join(output)