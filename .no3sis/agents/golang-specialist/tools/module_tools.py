"""
Go Module Management Tools

Tools for managing Go modules, dependencies, and project structure.
Handles go.mod analysis, dependency management, and module best practices.
"""

import os
import re
import json
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


def manage_dependencies(operation: str, module_name: Optional[str], config: Dict[str, Any]) -> str:
    """
    Manage Go module dependencies.

    Args:
        operation: Operation to perform (list, update, add, remove, tidy)
        module_name: Name of module for add/remove operations
        config: Agent configuration

    Returns:
        Operation result and status
    """
    try:
        # Find the module root
        module_root = _find_module_root(".")
        if not module_root:
            return "❌ No go.mod found in current directory or parents"

        result = {"operation": operation, "module_root": module_root}

        if operation == "list":
            deps = _list_dependencies(module_root, config)
            result["dependencies"] = deps
            return _format_dependency_list(result, config)

        elif operation == "update":
            update_result = _update_dependencies(module_root, module_name, config)
            result.update(update_result)
            return _format_update_result(result, config)

        elif operation == "add":
            if not module_name:
                return "❌ Module name required for add operation"
            add_result = _add_dependency(module_root, module_name, config)
            result.update(add_result)
            return _format_add_result(result, config)

        elif operation == "remove":
            if not module_name:
                return "❌ Module name required for remove operation"
            remove_result = _remove_dependency(module_root, module_name, config)
            result.update(remove_result)
            return _format_remove_result(result, config)

        elif operation == "tidy":
            tidy_result = _tidy_dependencies(module_root, config)
            result.update(tidy_result)
            return _format_tidy_result(result, config)

        else:
            return f"❌ Unknown operation: {operation}. Supported: list, update, add, remove, tidy"

    except Exception as e:
        return f"❌ Dependency management failed: {str(e)}"


def analyze_modules(project_path: str, check_vulnerabilities: bool, config: Dict[str, Any]) -> str:
    """
    Analyze Go module structure and dependencies.

    Args:
        project_path: Path to the Go project
        check_vulnerabilities: Whether to check for known vulnerabilities
        config: Agent configuration

    Returns:
        Comprehensive module analysis report
    """
    try:
        if not os.path.exists(project_path):
            return f"❌ Project path not found: {project_path}"

        analysis = {
            "project_path": project_path,
            "go_mod_info": None,
            "dependency_tree": None,
            "vulnerabilities": [],
            "recommendations": []
        }

        # Find and analyze go.mod
        go_mod_path = os.path.join(project_path, "go.mod")
        if os.path.exists(go_mod_path):
            mod_info = _analyze_go_mod(go_mod_path, config)
            analysis["go_mod_info"] = mod_info
        else:
            return f"❌ No go.mod found in {project_path}"

        # Analyze dependency tree
        dep_tree = _analyze_dependency_tree(project_path, config)
        analysis["dependency_tree"] = dep_tree

        # Check for vulnerabilities if requested
        if check_vulnerabilities:
            vulns = _check_vulnerabilities(project_path, config)
            analysis["vulnerabilities"] = vulns

        # Generate recommendations
        recommendations = _generate_module_recommendations(analysis, config)
        analysis["recommendations"] = recommendations

        return _format_module_analysis(analysis, config)

    except Exception as e:
        return f"❌ Module analysis failed: {str(e)}"


def _find_module_root(start_path: str) -> Optional[str]:
    """Find the module root by looking for go.mod file."""
    current_path = Path(start_path).absolute()

    while current_path != current_path.parent:
        go_mod = current_path / "go.mod"
        if go_mod.exists():
            return str(current_path)
        current_path = current_path.parent

    return None


def _list_dependencies(module_root: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """List all dependencies in the module."""
    try:
        # Run go list to get dependency information
        result = subprocess.run(
            ['go', 'list', '-m', '-json', 'all'],
            cwd=module_root,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode != 0:
            return {"error": result.stderr}

        # Parse JSON output
        dependencies = []
        for line in result.stdout.strip().split('\n'):
            if line.strip():
                try:
                    dep_info = json.loads(line)
                    dependencies.append(dep_info)
                except json.JSONDecodeError:
                    continue

        # Separate direct and indirect dependencies
        direct_deps = []
        indirect_deps = []

        for dep in dependencies:
            if dep.get('Main'):  # Skip the main module
                continue

            if dep.get('Indirect'):
                indirect_deps.append(dep)
            else:
                direct_deps.append(dep)

        return {
            "total": len(dependencies) - 1,  # Exclude main module
            "direct": direct_deps,
            "indirect": indirect_deps
        }

    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return {"error": str(e)}


def _update_dependencies(module_root: str, module_name: Optional[str], config: Dict[str, Any]) -> Dict[str, Any]:
    """Update dependencies in the module."""
    try:
        if module_name:
            # Update specific module
            result = subprocess.run(
                ['go', 'get', '-u', module_name],
                cwd=module_root,
                capture_output=True,
                text=True,
                timeout=60
            )
        else:
            # Update all dependencies
            result = subprocess.run(
                ['go', 'get', '-u', './...'],
                cwd=module_root,
                capture_output=True,
                text=True,
                timeout=60
            )

        return {
            "success": result.returncode == 0,
            "output": result.stdout,
            "error": result.stderr,
            "target": module_name or "all dependencies"
        }

    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}


def _add_dependency(module_root: str, module_name: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Add a new dependency to the module."""
    try:
        result = subprocess.run(
            ['go', 'get', module_name],
            cwd=module_root,
            capture_output=True,
            text=True,
            timeout=60
        )

        return {
            "success": result.returncode == 0,
            "module": module_name,
            "output": result.stdout,
            "error": result.stderr
        }

    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}


def _remove_dependency(module_root: str, module_name: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Remove a dependency from the module."""
    try:
        # First, remove imports from code (this is a simplified approach)
        # In practice, you'd want more sophisticated import removal

        # Remove from go.mod
        result = subprocess.run(
            ['go', 'mod', 'edit', '-droprequire', module_name],
            cwd=module_root,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0:
            # Run go mod tidy to clean up
            tidy_result = subprocess.run(
                ['go', 'mod', 'tidy'],
                cwd=module_root,
                capture_output=True,
                text=True,
                timeout=30
            )

            return {
                "success": tidy_result.returncode == 0,
                "module": module_name,
                "output": result.stdout + tidy_result.stdout,
                "error": result.stderr + tidy_result.stderr
            }

        return {
            "success": False,
            "module": module_name,
            "error": result.stderr
        }

    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}


def _tidy_dependencies(module_root: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Clean up the module dependencies."""
    try:
        result = subprocess.run(
            ['go', 'mod', 'tidy'],
            cwd=module_root,
            capture_output=True,
            text=True,
            timeout=30
        )

        return {
            "success": result.returncode == 0,
            "output": result.stdout,
            "error": result.stderr
        }

    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}


def _analyze_go_mod(go_mod_path: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze the go.mod file."""
    try:
        with open(go_mod_path, 'r', encoding='utf-8') as f:
            content = f.read()

        analysis = {
            "path": go_mod_path,
            "module_name": None,
            "go_version": None,
            "direct_dependencies": [],
            "replaced_modules": [],
            "excluded_modules": [],
            "toolchain": None
        }

        lines = content.splitlines()

        for line in lines:
            line = line.strip()

            if line.startswith('module '):
                analysis["module_name"] = line[7:].strip()
            elif line.startswith('go '):
                analysis["go_version"] = line[3:].strip()
            elif line.startswith('toolchain '):
                analysis["toolchain"] = line[10:].strip()
            elif line.startswith('require '):
                # Handle single line require
                req = line[8:].strip()
                if req and not req.startswith('('):
                    parts = req.split()
                    if len(parts) >= 2:
                        analysis["direct_dependencies"].append({
                            "name": parts[0],
                            "version": parts[1],
                            "indirect": "// indirect" in line
                        })
            elif line.startswith('replace '):
                replace_info = line[8:].strip()
                analysis["replaced_modules"].append(replace_info)
            elif line.startswith('exclude '):
                exclude_info = line[8:].strip()
                analysis["excluded_modules"].append(exclude_info)

        # Handle multi-line require blocks
        in_require_block = False
        for line in lines:
            line = line.strip()
            if line == 'require (':
                in_require_block = True
                continue
            elif line == ')' and in_require_block:
                in_require_block = False
                continue
            elif in_require_block and line and not line.startswith('//'):
                parts = line.split()
                if len(parts) >= 2:
                    analysis["direct_dependencies"].append({
                        "name": parts[0],
                        "version": parts[1],
                        "indirect": "// indirect" in line
                    })

        return analysis

    except Exception as e:
        return {"error": str(e)}


def _analyze_dependency_tree(project_path: str, config: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Analyze the full dependency tree."""
    try:
        # Get dependency graph
        result = subprocess.run(
            ['go', 'mod', 'graph'],
            cwd=project_path,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode != 0:
            return {"error": result.stderr}

        # Parse dependency graph
        dependencies = {}
        edges = []

        for line in result.stdout.strip().split('\n'):
            if line.strip() and ' ' in line:
                parts = line.strip().split(' ', 1)
                if len(parts) == 2:
                    from_mod, to_mod = parts
                    edges.append((from_mod, to_mod))

                    # Track all modules
                    dependencies[from_mod] = dependencies.get(from_mod, set())
                    dependencies[from_mod].add(to_mod)

        # Calculate metrics
        total_deps = len(dependencies)
        max_depth = _calculate_max_depth(dependencies)

        return {
            "total_modules": total_deps,
            "max_depth": max_depth,
            "edges": edges[:50],  # Limit output size
            "direct_count": len([k for k, v in dependencies.items() if v])
        }

    except (subprocess.TimeoutExpired, FileNotFoundError):
        return None


def _check_vulnerabilities(project_path: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check for known vulnerabilities using govulncheck if available."""
    vulnerabilities = []

    try:
        # Try to run govulncheck
        result = subprocess.run(
            ['govulncheck', './...'],
            cwd=project_path,
            capture_output=True,
            text=True,
            timeout=60
        )

        if result.returncode == 0:
            vulnerabilities.append({
                "status": "clean",
                "message": "No known vulnerabilities found"
            })
        else:
            # Parse vulnerability output
            output = result.stdout + result.stderr
            if "Found" in output or "vulnerability" in output.lower():
                vulnerabilities.append({
                    "status": "vulnerable",
                    "message": "Vulnerabilities found",
                    "details": output[:500]  # Truncate for safety
                })

    except (subprocess.TimeoutExpired, FileNotFoundError):
        # govulncheck not available
        vulnerabilities.append({
            "status": "unknown",
            "message": "govulncheck not available - install with: go install golang.org/x/vuln/cmd/govulncheck@latest"
        })

    return vulnerabilities


def _calculate_max_depth(dependencies: Dict[str, set]) -> int:
    """Calculate the maximum dependency depth."""
    def dfs_depth(module: str, visited: set) -> int:
        if module in visited:
            return 0  # Avoid cycles

        visited.add(module)
        deps = dependencies.get(module, set())

        if not deps:
            return 1

        max_child_depth = 0
        for dep in deps:
            child_depth = dfs_depth(dep, visited.copy())
            max_child_depth = max(max_child_depth, child_depth)

        return max_child_depth + 1

    max_depth = 0
    for root_module in dependencies:
        depth = dfs_depth(root_module, set())
        max_depth = max(max_depth, depth)

    return max_depth


def _generate_module_recommendations(analysis: Dict[str, Any], config: Dict[str, Any]) -> List[str]:
    """Generate module management recommendations."""
    recommendations = []

    go_mod_info = analysis.get("go_mod_info")
    if not go_mod_info:
        return recommendations

    # Check Go version
    go_version = go_mod_info.get("go_version")
    if go_version:
        try:
            version_parts = go_version.split(".")
            if len(version_parts) >= 2:
                major, minor = int(version_parts[0]), int(version_parts[1])
                if major == 1 and minor < 19:  # Assume current best practice
                    recommendations.append(
                        f"Consider updating Go version from {go_version} to a more recent version"
                    )
        except (ValueError, IndexError):
            pass

    # Check dependency count
    direct_deps = go_mod_info.get("direct_dependencies", [])
    direct_count = len([d for d in direct_deps if not d.get("indirect")])

    if direct_count > 20:
        recommendations.append(
            f"High number of direct dependencies ({direct_count}). Consider if all are necessary."
        )

    # Check for replaced modules
    replaced = go_mod_info.get("replaced_modules", [])
    if replaced:
        recommendations.append(
            f"Found {len(replaced)} replaced modules. Ensure replacements are still needed."
        )

    # Check dependency tree
    dep_tree = analysis.get("dependency_tree")
    if dep_tree and "max_depth" in dep_tree:
        max_depth = dep_tree["max_depth"]
        if max_depth > 10:
            recommendations.append(
                f"Deep dependency tree (depth {max_depth}). Monitor for diamond dependency issues."
            )

    # Check vulnerabilities
    vulnerabilities = analysis.get("vulnerabilities", [])
    for vuln in vulnerabilities:
        if vuln.get("status") == "vulnerable":
            recommendations.append(
                "Vulnerabilities found. Run 'go get -u' to update dependencies and fix issues."
            )
            break

    return recommendations


def _format_dependency_list(result: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the dependency list result."""
    report = "# Go Module Dependencies\n\n"
    report += f"**Module Root:** `{result['module_root']}`\n\n"

    deps = result["dependencies"]
    if "error" in deps:
        return f"❌ Failed to list dependencies: {deps['error']}\n"

    report += f"## Summary\n\n"
    report += f"- **Total Dependencies:** {deps['total']}\n"
    report += f"- **Direct Dependencies:** {len(deps['direct'])}\n"
    report += f"- **Indirect Dependencies:** {len(deps['indirect'])}\n\n"

    # Direct dependencies
    direct_deps = deps["direct"]
    if direct_deps:
        report += f"## Direct Dependencies ({len(direct_deps)})\n\n"
        for dep in direct_deps:
            name = dep.get("Path", "unknown")
            version = dep.get("Version", "unknown")
            report += f"- `{name}` @ `{version}`\n"
        report += "\n"

    # Show some indirect dependencies
    indirect_deps = deps["indirect"][:10]  # Limit to first 10
    if indirect_deps:
        report += f"## Indirect Dependencies (showing {len(indirect_deps)} of {len(deps['indirect'])})\n\n"
        for dep in indirect_deps:
            name = dep.get("Path", "unknown")
            version = dep.get("Version", "unknown")
            report += f"- `{name}` @ `{version}`\n"

        if len(deps['indirect']) > 10:
            report += f"... and {len(deps['indirect']) - 10} more\n"
        report += "\n"

    return report


def _format_update_result(result: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the dependency update result."""
    target = result.get("target", "dependencies")
    success = result.get("success", False)

    if success:
        report = f"✅ Successfully updated {target}\n\n"
        if result.get("output"):
            report += f"**Output:**\n```\n{result['output']}\n```\n"
    else:
        report = f"❌ Failed to update {target}\n\n"
        if result.get("error"):
            report += f"**Error:**\n```\n{result['error']}\n```\n"

    return report


def _format_add_result(result: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the add dependency result."""
    module = result.get("module", "unknown")
    success = result.get("success", False)

    if success:
        report = f"✅ Successfully added dependency `{module}`\n\n"
        if result.get("output"):
            report += f"**Output:**\n```\n{result['output']}\n```\n"
    else:
        report = f"❌ Failed to add dependency `{module}`\n\n"
        if result.get("error"):
            report += f"**Error:**\n```\n{result['error']}\n```\n"

    return report


def _format_remove_result(result: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the remove dependency result."""
    module = result.get("module", "unknown")
    success = result.get("success", False)

    if success:
        report = f"✅ Successfully removed dependency `{module}`\n\n"
        if result.get("output"):
            report += f"**Output:**\n```\n{result['output']}\n```\n"
    else:
        report = f"❌ Failed to remove dependency `{module}`\n\n"
        if result.get("error"):
            report += f"**Error:**\n```\n{result['error']}\n```\n"

    return report


def _format_tidy_result(result: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the tidy dependencies result."""
    success = result.get("success", False)

    if success:
        report = "✅ Successfully tidied module dependencies\n\n"
        if result.get("output"):
            report += f"**Output:**\n```\n{result['output']}\n```\n"
    else:
        report = "❌ Failed to tidy dependencies\n\n"
        if result.get("error"):
            report += f"**Error:**\n```\n{result['error']}\n```\n"

    return report


def _format_module_analysis(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the complete module analysis."""
    report = "# Go Module Analysis Report\n\n"
    report += f"**Project:** `{analysis['project_path']}`\n\n"

    # go.mod information
    go_mod_info = analysis.get("go_mod_info")
    if go_mod_info:
        if "error" in go_mod_info:
            report += f"❌ go.mod analysis failed: {go_mod_info['error']}\n\n"
        else:
            report += "## Module Information\n\n"
            report += f"- **Module Name:** `{go_mod_info.get('module_name', 'unknown')}`\n"
            report += f"- **Go Version:** `{go_mod_info.get('go_version', 'unknown')}`\n"

            if go_mod_info.get("toolchain"):
                report += f"- **Toolchain:** `{go_mod_info['toolchain']}`\n"

            direct_deps = go_mod_info.get("direct_dependencies", [])
            non_indirect_deps = [d for d in direct_deps if not d.get("indirect")]
            indirect_deps = [d for d in direct_deps if d.get("indirect")]

            report += f"- **Direct Dependencies:** {len(non_indirect_deps)}\n"
            report += f"- **Indirect Dependencies:** {len(indirect_deps)}\n"

            if go_mod_info.get("replaced_modules"):
                report += f"- **Replaced Modules:** {len(go_mod_info['replaced_modules'])}\n"
            if go_mod_info.get("excluded_modules"):
                report += f"- **Excluded Modules:** {len(go_mod_info['excluded_modules'])}\n"

            report += "\n"

            # Show direct dependencies
            if non_indirect_deps:
                report += f"### Direct Dependencies ({len(non_indirect_deps)})\n\n"
                for dep in non_indirect_deps[:10]:  # Show first 10
                    report += f"- `{dep['name']}` @ `{dep['version']}`\n"
                if len(non_indirect_deps) > 10:
                    report += f"... and {len(non_indirect_deps) - 10} more\n"
                report += "\n"

    # Dependency tree analysis
    dep_tree = analysis.get("dependency_tree")
    if dep_tree:
        if "error" in dep_tree:
            report += f"⚠️ Dependency tree analysis failed: {dep_tree['error']}\n\n"
        else:
            report += "## Dependency Tree Analysis\n\n"
            report += f"- **Total Modules:** {dep_tree.get('total_modules', 0)}\n"
            report += f"- **Maximum Depth:** {dep_tree.get('max_depth', 0)}\n"
            report += f"- **Direct Dependencies:** {dep_tree.get('direct_count', 0)}\n\n"

    # Vulnerability information
    vulnerabilities = analysis.get("vulnerabilities", [])
    if vulnerabilities:
        report += "## Security Analysis\n\n"
        for vuln in vulnerabilities:
            status = vuln.get("status", "unknown")
            icon = {"clean": "✅", "vulnerable": "❌", "unknown": "❓"}.get(status, "❓")

            report += f"{icon} **Status:** {status}\n"
            report += f"   {vuln.get('message', 'No message')}\n"

            if vuln.get("details"):
                report += f"   **Details:** {vuln['details'][:200]}...\n"
            report += "\n"

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        report += "## Recommendations\n\n"
        for rec in recommendations:
            report += f"- 💡 {rec}\n"
        report += "\n"

    return report