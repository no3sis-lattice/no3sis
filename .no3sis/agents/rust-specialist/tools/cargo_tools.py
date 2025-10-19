"""
Rust Cargo and Ecosystem Tools

Tools for analyzing Cargo projects, dependencies, build configuration,
and the broader Rust ecosystem integration.
"""

import json
import subprocess
import toml
from pathlib import Path
from typing import Dict, Any, List, Optional


async def analyze_cargo_project(project_path: str) -> Dict[str, Any]:
    """
    Analyze Cargo project structure and configuration.

    Args:
        project_path: Path to Cargo project directory

    Returns:
        Dict with Cargo project analysis results
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

        analysis = await _comprehensive_cargo_analysis(str(path))

        formatted_output = _format_cargo_analysis_results(analysis)

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
                "text": f"❌ Cargo project analysis failed for {project_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def check_dependencies(project_path: str, check_outdated: bool = True) -> Dict[str, Any]:
    """
    Analyze project dependencies for security and updates.

    Args:
        project_path: Path to Cargo project directory
        check_outdated: Whether to check for outdated dependencies

    Returns:
        Dict with dependency analysis results
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

        analysis = await _analyze_dependencies(str(path), check_outdated)

        formatted_output = _format_dependency_analysis_results(analysis)

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
                "text": f"❌ Dependency analysis failed for {project_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def optimize_build_config(project_path: str) -> Dict[str, Any]:
    """
    Optimize Cargo build configuration for performance.

    Args:
        project_path: Path to Cargo project directory

    Returns:
        Dict with build optimization suggestions
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

        analysis = await _analyze_build_optimization(str(path))

        formatted_output = _format_build_optimization_results(analysis)

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
                "text": f"❌ Build optimization analysis failed for {project_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _comprehensive_cargo_analysis(project_path: str) -> Dict[str, Any]:
    """Perform comprehensive Cargo project analysis."""
    path = Path(project_path)

    # Load Cargo.toml
    cargo_toml = _load_cargo_toml(path)

    # Project structure analysis
    structure = _analyze_project_structure(path)

    # Workspace analysis
    workspace = _analyze_workspace_structure(path, cargo_toml)

    # Feature analysis
    features = _analyze_feature_configuration(cargo_toml)

    # Profile analysis
    profiles = _analyze_build_profiles(cargo_toml)

    # Metadata analysis
    metadata = _analyze_project_metadata(cargo_toml)

    return {
        "cargo_toml": cargo_toml,
        "structure": structure,
        "workspace": workspace,
        "features": features,
        "profiles": profiles,
        "metadata": metadata,
        "recommendations": _generate_cargo_recommendations(
            cargo_toml, structure, workspace, features, profiles
        )
    }


def _load_cargo_toml(project_path: Path) -> Optional[Dict[str, Any]]:
    """Load and parse Cargo.toml file."""
    cargo_toml_path = project_path / "Cargo.toml"

    if not cargo_toml_path.exists():
        return None

    try:
        with open(cargo_toml_path, 'r') as f:
            return toml.load(f)
    except Exception as e:
        return {"error": f"Failed to parse Cargo.toml: {str(e)}"}


def _analyze_project_structure(project_path: Path) -> Dict[str, Any]:
    """Analyze Cargo project directory structure."""
    structure = {
        "has_src": (project_path / "src").exists(),
        "has_lib": (project_path / "src" / "lib.rs").exists(),
        "has_main": (project_path / "src" / "main.rs").exists(),
        "has_tests": (project_path / "tests").exists(),
        "has_benches": (project_path / "benches").exists(),
        "has_examples": (project_path / "examples").exists(),
        "has_docs": (project_path / "docs").exists() or (project_path / "README.md").exists(),
        "has_ci": (project_path / ".github" / "workflows").exists() or (project_path / ".gitlab-ci.yml").exists(),
        "project_type": "unknown"
    }

    # Determine project type
    if structure["has_lib"] and structure["has_main"]:
        structure["project_type"] = "binary_and_library"
    elif structure["has_lib"]:
        structure["project_type"] = "library"
    elif structure["has_main"]:
        structure["project_type"] = "binary"

    # Count source files
    if structure["has_src"]:
        src_path = project_path / "src"
        structure["source_files"] = len(list(src_path.glob("**/*.rs")))
    else:
        structure["source_files"] = 0

    # Count test files
    if structure["has_tests"]:
        tests_path = project_path / "tests"
        structure["test_files"] = len(list(tests_path.glob("**/*.rs")))
    else:
        structure["test_files"] = 0

    # Count example files
    if structure["has_examples"]:
        examples_path = project_path / "examples"
        structure["example_files"] = len(list(examples_path.glob("**/*.rs")))
    else:
        structure["example_files"] = 0

    return structure


def _analyze_workspace_structure(project_path: Path, cargo_toml: Optional[Dict]) -> Dict[str, Any]:
    """Analyze workspace configuration."""
    workspace_info = {
        "is_workspace": False,
        "is_member": False,
        "members": [],
        "workspace_root": None
    }

    if not cargo_toml:
        return workspace_info

    # Check if this is a workspace root
    if "workspace" in cargo_toml:
        workspace_info["is_workspace"] = True
        workspace_members = cargo_toml["workspace"].get("members", [])
        workspace_info["members"] = workspace_members

        # Check if member directories exist
        existing_members = []
        for member in workspace_members:
            member_path = project_path / member
            if member_path.exists() and (member_path / "Cargo.toml").exists():
                existing_members.append(member)

        workspace_info["existing_members"] = existing_members

    # Check if this is a workspace member
    parent = project_path.parent
    while parent != parent.parent:  # Not root
        parent_cargo = parent / "Cargo.toml"
        if parent_cargo.exists():
            try:
                with open(parent_cargo, 'r') as f:
                    parent_toml = toml.load(f)
                    if "workspace" in parent_toml:
                        workspace_info["is_member"] = True
                        workspace_info["workspace_root"] = str(parent)
                        break
            except:
                pass
        parent = parent.parent

    return workspace_info


def _analyze_feature_configuration(cargo_toml: Optional[Dict]) -> Dict[str, Any]:
    """Analyze Cargo feature configuration."""
    features_info = {
        "has_features": False,
        "features": {},
        "default_features": [],
        "feature_count": 0
    }

    if not cargo_toml:
        return features_info

    if "features" in cargo_toml:
        features_info["has_features"] = True
        features = cargo_toml["features"]
        features_info["features"] = features
        features_info["feature_count"] = len(features)

        if "default" in features:
            features_info["default_features"] = features["default"]

        # Analyze feature complexity
        features_info["complex_features"] = []
        for name, deps in features.items():
            if isinstance(deps, list) and len(deps) > 3:
                features_info["complex_features"].append(name)

    return features_info


def _analyze_build_profiles(cargo_toml: Optional[Dict]) -> Dict[str, Any]:
    """Analyze Cargo build profiles."""
    profiles_info = {
        "has_custom_profiles": False,
        "profiles": {},
        "optimizations": {}
    }

    if not cargo_toml:
        return profiles_info

    if "profile" in cargo_toml:
        profiles_info["has_custom_profiles"] = True
        profiles = cargo_toml["profile"]
        profiles_info["profiles"] = profiles

        # Check for common optimizations
        for profile_name, config in profiles.items():
            if isinstance(config, dict):
                optimizations = {}

                if "lto" in config:
                    optimizations["lto"] = config["lto"]
                if "codegen-units" in config:
                    optimizations["codegen_units"] = config["codegen-units"]
                if "opt-level" in config:
                    optimizations["opt_level"] = config["opt-level"]
                if "debug" in config:
                    optimizations["debug"] = config["debug"]
                if "panic" in config:
                    optimizations["panic"] = config["panic"]

                if optimizations:
                    profiles_info["optimizations"][profile_name] = optimizations

    return profiles_info


def _analyze_project_metadata(cargo_toml: Optional[Dict]) -> Dict[str, Any]:
    """Analyze project metadata."""
    metadata = {
        "has_metadata": False,
        "name": None,
        "version": None,
        "authors": [],
        "description": None,
        "license": None,
        "repository": None,
        "documentation": None,
        "homepage": None,
        "readme": None,
        "keywords": [],
        "categories": [],
        "edition": None,
        "rust_version": None
    }

    if not cargo_toml or "package" not in cargo_toml:
        return metadata

    package = cargo_toml["package"]
    metadata["has_metadata"] = True

    # Extract metadata fields
    metadata_fields = [
        "name", "version", "description", "license", "repository",
        "documentation", "homepage", "readme", "edition", "rust-version"
    ]

    for field in metadata_fields:
        if field in package:
            key = field.replace("-", "_")
            metadata[key] = package[field]

    # Handle array fields
    if "authors" in package:
        metadata["authors"] = package["authors"] if isinstance(package["authors"], list) else [package["authors"]]

    if "keywords" in package:
        metadata["keywords"] = package["keywords"] if isinstance(package["keywords"], list) else []

    if "categories" in package:
        metadata["categories"] = package["categories"] if isinstance(package["categories"], list) else []

    return metadata


async def _analyze_dependencies(project_path: str, check_outdated: bool) -> Dict[str, Any]:
    """Analyze project dependencies."""
    path = Path(project_path)
    cargo_toml = _load_cargo_toml(path)

    analysis = {
        "dependencies": _extract_dependencies(cargo_toml),
        "security_audit": await _run_security_audit(project_path) if check_outdated else None,
        "outdated_check": await _check_outdated_dependencies(project_path) if check_outdated else None,
        "dependency_tree": await _analyze_dependency_tree(project_path)
    }

    return analysis


def _extract_dependencies(cargo_toml: Optional[Dict]) -> Dict[str, Any]:
    """Extract dependency information from Cargo.toml."""
    deps_info = {
        "dependencies": {},
        "dev_dependencies": {},
        "build_dependencies": {},
        "total_count": 0,
        "version_patterns": {}
    }

    if not cargo_toml:
        return deps_info

    # Extract different types of dependencies
    dep_sections = ["dependencies", "dev-dependencies", "build-dependencies"]
    dep_keys = ["dependencies", "dev_dependencies", "build_dependencies"]

    for section, key in zip(dep_sections, dep_keys):
        if section in cargo_toml:
            deps = cargo_toml[section]
            deps_info[key] = deps
            deps_info["total_count"] += len(deps)

            # Analyze version patterns
            for name, spec in deps.items():
                version_pattern = _analyze_version_spec(spec)
                if version_pattern:
                    if version_pattern not in deps_info["version_patterns"]:
                        deps_info["version_patterns"][version_pattern] = 0
                    deps_info["version_patterns"][version_pattern] += 1

    return deps_info


def _analyze_version_spec(spec) -> Optional[str]:
    """Analyze version specification pattern."""
    if isinstance(spec, str):
        if spec.startswith("^"):
            return "caret"
        elif spec.startswith("~"):
            return "tilde"
        elif spec.startswith("="):
            return "exact"
        elif "*" in spec:
            return "wildcard"
        else:
            return "basic"
    elif isinstance(spec, dict):
        if "git" in spec:
            return "git"
        elif "path" in spec:
            return "path"
        elif "version" in spec:
            return _analyze_version_spec(spec["version"])

    return None


async def _run_security_audit(project_path: str) -> Optional[Dict[str, Any]]:
    """Run cargo audit for security vulnerabilities."""
    try:
        result = subprocess.run(
            ["cargo", "audit", "--json"],
            cwd=project_path,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0:
            return {"vulnerabilities": [], "status": "clean"}
        else:
            # Try to parse audit output
            if result.stdout:
                try:
                    audit_data = json.loads(result.stdout)
                    return audit_data
                except:
                    pass

            return {
                "vulnerabilities": [],
                "status": "error",
                "message": result.stderr or "Audit failed"
            }

    except Exception as e:
        return {
            "status": "unavailable",
            "message": f"cargo audit not available: {str(e)}"
        }


async def _check_outdated_dependencies(project_path: str) -> Optional[Dict[str, Any]]:
    """Check for outdated dependencies."""
    try:
        result = subprocess.run(
            ["cargo", "outdated", "--format", "json"],
            cwd=project_path,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0 and result.stdout:
            try:
                return json.loads(result.stdout)
            except:
                pass

        return {
            "status": "unavailable",
            "message": "cargo outdated not available"
        }

    except Exception:
        return None


async def _analyze_dependency_tree(project_path: str) -> Dict[str, Any]:
    """Analyze dependency tree structure."""
    try:
        result = subprocess.run(
            ["cargo", "tree", "--format", "{p}"],
            cwd=project_path,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0:
            lines = result.stdout.strip().split('\n')
            return {
                "total_dependencies": len(lines) - 1,  # Exclude root package
                "depth_analysis": _analyze_tree_depth(lines),
                "duplicate_detection": _detect_duplicate_dependencies(lines)
            }

    except Exception:
        pass

    return {"status": "unavailable"}


def _analyze_tree_depth(tree_lines: List[str]) -> Dict[str, Any]:
    """Analyze dependency tree depth."""
    max_depth = 0
    depth_counts = {}

    for line in tree_lines:
        depth = (len(line) - len(line.lstrip())) // 4  # Assuming 4-space indentation
        max_depth = max(max_depth, depth)

        if depth not in depth_counts:
            depth_counts[depth] = 0
        depth_counts[depth] += 1

    return {
        "max_depth": max_depth,
        "depth_distribution": depth_counts
    }


def _detect_duplicate_dependencies(tree_lines: List[str]) -> Dict[str, Any]:
    """Detect duplicate dependencies in the tree."""
    package_counts = {}
    duplicates = []

    for line in tree_lines:
        # Extract package name (simplified)
        package = line.strip().split(' ')[0] if line.strip() else ""
        if package and not package.startswith('├') and not package.startswith('└'):
            if package in package_counts:
                package_counts[package] += 1
                if package_counts[package] == 2:  # First duplicate
                    duplicates.append(package)
            else:
                package_counts[package] = 1

    return {
        "duplicate_count": len(duplicates),
        "duplicates": duplicates[:10]  # Limit to first 10
    }


async def _analyze_build_optimization(project_path: str) -> Dict[str, Any]:
    """Analyze build optimization opportunities."""
    path = Path(project_path)
    cargo_toml = _load_cargo_toml(path)

    optimization_analysis = {
        "current_profiles": _analyze_build_profiles(cargo_toml),
        "optimization_opportunities": _identify_optimization_opportunities(cargo_toml),
        "build_time_analysis": await _analyze_build_performance(project_path),
        "target_analysis": _analyze_compilation_targets(cargo_toml)
    }

    return optimization_analysis


def _identify_optimization_opportunities(cargo_toml: Optional[Dict]) -> List[Dict[str, Any]]:
    """Identify build optimization opportunities."""
    opportunities = []

    if not cargo_toml:
        return opportunities

    profiles = cargo_toml.get("profile", {})

    # Check release profile optimizations
    release_profile = profiles.get("release", {})

    if not release_profile.get("lto"):
        opportunities.append({
            "type": "lto",
            "priority": "high",
            "message": "Enable Link Time Optimization (LTO) for release builds",
            "suggestion": 'Add `lto = true` to [profile.release]',
            "benefit": "Significant performance improvements in release builds"
        })

    if release_profile.get("codegen-units", 16) > 1:
        opportunities.append({
            "type": "codegen_units",
            "priority": "medium",
            "message": "Reduce codegen-units for better optimization",
            "suggestion": 'Set `codegen-units = 1` in [profile.release]',
            "benefit": "Better optimization at the cost of longer compile times"
        })

    if release_profile.get("panic") != "abort":
        opportunities.append({
            "type": "panic_strategy",
            "priority": "low",
            "message": "Consider panic = 'abort' for smaller binaries",
            "suggestion": 'Add `panic = "abort"` to [profile.release]',
            "benefit": "Smaller binary size by removing unwinding code"
        })

    # Check dev profile optimizations
    dev_profile = profiles.get("dev", {})

    if dev_profile.get("debug") != 1:
        opportunities.append({
            "type": "debug_info",
            "priority": "low",
            "message": "Optimize debug info for faster builds",
            "suggestion": 'Set `debug = 1` in [profile.dev] for line numbers only',
            "benefit": "Faster compilation with basic debugging info"
        })

    # Check for missing profiles
    if "bench" not in profiles:
        opportunities.append({
            "type": "bench_profile",
            "priority": "low",
            "message": "Add benchmark profile for performance testing",
            "suggestion": "Add [profile.bench] with optimizations similar to release",
            "benefit": "Optimized benchmarks for accurate performance measurement"
        })

    return opportunities


async def _analyze_build_performance(project_path: str) -> Dict[str, Any]:
    """Analyze build performance characteristics."""
    # This would require actual build timing, so we provide a simplified analysis
    path = Path(project_path)

    analysis = {
        "source_complexity": _estimate_build_complexity(path),
        "dependency_impact": _estimate_dependency_build_impact(path),
        "suggestions": []
    }

    # Add suggestions based on complexity
    if analysis["source_complexity"]["file_count"] > 100:
        analysis["suggestions"].append({
            "type": "compilation_speed",
            "message": "Large project detected - consider parallel compilation",
            "suggestion": "Use `cargo build -j <num_cores>` or set CARGO_BUILD_JOBS"
        })

    return analysis


def _estimate_build_complexity(project_path: Path) -> Dict[str, Any]:
    """Estimate build complexity based on source files."""
    src_path = project_path / "src"

    if not src_path.exists():
        return {"file_count": 0, "complexity": "unknown"}

    rust_files = list(src_path.glob("**/*.rs"))
    total_lines = 0

    for file in rust_files[:20]:  # Limit to first 20 files
        try:
            total_lines += len(file.read_text().split('\n'))
        except:
            continue

    return {
        "file_count": len(rust_files),
        "estimated_lines": total_lines,
        "complexity": "high" if len(rust_files) > 50 else "medium" if len(rust_files) > 10 else "low"
    }


def _estimate_dependency_build_impact(project_path: Path) -> Dict[str, Any]:
    """Estimate build impact of dependencies."""
    cargo_toml = _load_cargo_toml(project_path)

    if not cargo_toml:
        return {"impact": "unknown"}

    deps = cargo_toml.get("dependencies", {})
    heavy_deps = []

    # List of known heavy dependencies
    known_heavy = ["serde", "tokio", "clap", "diesel", "actix-web", "warp", "rocket"]

    for dep_name in deps:
        if dep_name in known_heavy:
            heavy_deps.append(dep_name)

    return {
        "total_dependencies": len(deps),
        "heavy_dependencies": heavy_deps,
        "impact": "high" if len(heavy_deps) > 3 else "medium" if len(heavy_deps) > 1 else "low"
    }


def _analyze_compilation_targets(cargo_toml: Optional[Dict]) -> Dict[str, Any]:
    """Analyze compilation target configuration."""
    if not cargo_toml:
        return {"targets": []}

    targets = []

    # Check for binary targets
    if "bin" in cargo_toml:
        bin_targets = cargo_toml["bin"]
        if isinstance(bin_targets, list):
            targets.extend([{"type": "bin", "name": t.get("name", "unknown")} for t in bin_targets])

    # Check for library target
    if "lib" in cargo_toml:
        targets.append({"type": "lib", "name": cargo_toml["lib"].get("name", "lib")})

    # Check package metadata for binaries
    if "package" in cargo_toml and targets == []:
        # Default binary target exists if src/main.rs exists
        targets.append({"type": "bin", "name": cargo_toml["package"].get("name", "main")})

    return {
        "targets": targets,
        "target_count": len(targets)
    }


def _generate_cargo_recommendations(cargo_toml: Optional[Dict], structure: Dict,
                                   workspace: Dict, features: Dict, profiles: Dict) -> List[Dict[str, Any]]:
    """Generate Cargo project recommendations."""
    recommendations = []

    # Project structure recommendations
    if structure.get("project_type") == "unknown":
        recommendations.append({
            "type": "project_structure",
            "priority": "high",
            "message": "Project structure unclear - ensure src/main.rs or src/lib.rs exists",
            "suggestion": "Create appropriate entry point file for your project type"
        })

    if not structure.get("has_tests") and structure.get("source_files", 0) > 5:
        recommendations.append({
            "type": "testing",
            "priority": "medium",
            "message": "No tests directory found for non-trivial project",
            "suggestion": "Create tests/ directory with integration tests"
        })

    # Workspace recommendations
    if not workspace.get("is_workspace") and structure.get("source_files", 0) > 50:
        recommendations.append({
            "type": "workspace",
            "priority": "medium",
            "message": "Large project could benefit from workspace organization",
            "suggestion": "Consider splitting into multiple crates using Cargo workspaces"
        })

    # Features recommendations
    if not features.get("has_features") and structure.get("project_type") == "library":
        recommendations.append({
            "type": "features",
            "priority": "low",
            "message": "Library without feature flags",
            "suggestion": "Consider adding feature flags for optional functionality"
        })

    # Profile recommendations
    if not profiles.get("has_custom_profiles"):
        recommendations.append({
            "type": "build_optimization",
            "priority": "medium",
            "message": "No custom build profiles defined",
            "suggestion": "Add optimized release profile with LTO and reduced codegen-units"
        })

    # Metadata recommendations
    if cargo_toml and "package" in cargo_toml:
        package = cargo_toml["package"]
        if not package.get("description"):
            recommendations.append({
                "type": "metadata",
                "priority": "low",
                "message": "Missing package description",
                "suggestion": "Add description field to package metadata"
            })

        if not package.get("license"):
            recommendations.append({
                "type": "metadata",
                "priority": "medium",
                "message": "No license specified",
                "suggestion": "Add license field to package metadata"
            })

    return recommendations


# Formatting functions

def _format_cargo_analysis_results(analysis: Dict[str, Any]) -> str:
    """Format Cargo analysis results for display."""
    output = []

    output.append("📦 **Cargo Project Analysis**\n")

    # Project structure
    structure = analysis.get("structure", {})
    output.append(f"🏗️ **Project Structure:**")
    output.append(f"- Type: {structure.get('project_type', 'unknown')}")
    output.append(f"- Source files: {structure.get('source_files', 0)}")
    output.append(f"- Test files: {structure.get('test_files', 0)}")
    output.append(f"- Examples: {structure.get('example_files', 0)}")

    features = ["has_lib", "has_main", "has_tests", "has_benches", "has_examples", "has_docs", "has_ci"]
    enabled_features = [feature.replace("has_", "").title() for feature in features if structure.get(feature, False)]
    if enabled_features:
        output.append(f"- Features: {', '.join(enabled_features)}")
    output.append("")

    # Workspace info
    workspace = analysis.get("workspace", {})
    if workspace.get("is_workspace"):
        output.append(f"👥 **Workspace:** Root with {len(workspace.get('members', []))} members")
    elif workspace.get("is_member"):
        output.append(f"👤 **Workspace Member:** Part of workspace at {workspace.get('workspace_root')}")
    output.append("")

    # Features
    features_info = analysis.get("features", {})
    if features_info.get("has_features"):
        output.append(f"🎛️ **Features:** {features_info.get('feature_count', 0)} defined")
        default_features = features_info.get("default_features", [])
        if default_features:
            output.append(f"- Default: {', '.join(default_features)}")
        output.append("")

    # Build profiles
    profiles_info = analysis.get("profiles", {})
    if profiles_info.get("has_custom_profiles"):
        output.append("⚙️ **Custom Build Profiles:**")
        profiles = profiles_info.get("profiles", {})
        for profile_name in profiles.keys():
            output.append(f"- {profile_name}")

        optimizations = profiles_info.get("optimizations", {})
        if optimizations:
            output.append("Optimizations:")
            for profile, opts in optimizations.items():
                opt_list = [f"{k}={v}" for k, v in opts.items()]
                output.append(f"  - {profile}: {', '.join(opt_list)}")
        output.append("")

    # Metadata
    metadata = analysis.get("metadata", {})
    if metadata.get("has_metadata"):
        output.append("📋 **Package Metadata:**")
        if metadata.get("version"):
            output.append(f"- Version: {metadata['version']}")
        if metadata.get("edition"):
            output.append(f"- Edition: {metadata['edition']}")
        if metadata.get("license"):
            output.append(f"- License: {metadata['license']}")
        if metadata.get("description"):
            output.append(f"- Description: {metadata['description'][:60]}...")
        output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("suggestion"):
                output.append(f"   💡 {rec['suggestion']}")
        output.append("")

    return '\n'.join(output)


def _format_dependency_analysis_results(analysis: Dict[str, Any]) -> str:
    """Format dependency analysis results for display."""
    output = []

    output.append("📚 **Dependency Analysis**\n")

    # Dependencies overview
    deps = analysis.get("dependencies", {})
    output.append("📊 **Dependencies Overview:**")
    output.append(f"- Dependencies: {len(deps.get('dependencies', {}))}")
    output.append(f"- Dev dependencies: {len(deps.get('dev_dependencies', {}))}")
    output.append(f"- Build dependencies: {len(deps.get('build_dependencies', {}))}")
    output.append(f"- Total: {deps.get('total_count', 0)}")
    output.append("")

    # Version patterns
    version_patterns = deps.get("version_patterns", {})
    if version_patterns:
        output.append("📋 **Version Patterns:**")
        for pattern, count in version_patterns.items():
            output.append(f"- {pattern}: {count}")
        output.append("")

    # Security audit
    security = analysis.get("security_audit")
    if security:
        status = security.get("status", "unknown")
        if status == "clean":
            output.append("🛡️ **Security Audit:** ✅ Clean")
        elif status == "error":
            vulnerabilities = security.get("vulnerabilities", [])
            output.append(f"🚨 **Security Issues:** {len(vulnerabilities)} found")
        else:
            output.append(f"⚠️ **Security Audit:** {security.get('message', 'Unavailable')}")
        output.append("")

    # Outdated dependencies
    outdated = analysis.get("outdated_check")
    if outdated and outdated.get("status") != "unavailable":
        # Simplified outdated analysis
        output.append("📅 **Outdated Check:** Available")
        output.append("")

    # Dependency tree
    tree = analysis.get("dependency_tree", {})
    if "total_dependencies" in tree:
        output.append("🌳 **Dependency Tree:**")
        output.append(f"- Total dependencies: {tree['total_dependencies']}")

        depth_analysis = tree.get("depth_analysis", {})
        if depth_analysis:
            max_depth = depth_analysis.get("max_depth", 0)
            output.append(f"- Maximum depth: {max_depth}")

        duplicate_detection = tree.get("duplicate_detection", {})
        duplicate_count = duplicate_detection.get("duplicate_count", 0)
        if duplicate_count > 0:
            output.append(f"⚠️ Duplicate dependencies: {duplicate_count}")
            duplicates = duplicate_detection.get("duplicates", [])[:5]
            for dup in duplicates:
                output.append(f"  - {dup}")
        output.append("")

    return '\n'.join(output)


def _format_build_optimization_results(analysis: Dict[str, Any]) -> str:
    """Format build optimization results for display."""
    output = []

    output.append("⚡ **Build Optimization Analysis**\n")

    # Current profiles
    current_profiles = analysis.get("current_profiles", {})
    if current_profiles.get("has_custom_profiles"):
        output.append("⚙️ **Current Profiles:**")
        optimizations = current_profiles.get("optimizations", {})
        for profile, opts in optimizations.items():
            output.append(f"- {profile}: {len(opts)} optimizations")
        output.append("")

    # Optimization opportunities
    opportunities = analysis.get("optimization_opportunities", [])
    if opportunities:
        output.append("💡 **Optimization Opportunities:**")
        for opp in opportunities:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(opp.get("priority"), "⚪")
            output.append(f"{priority_emoji} {opp.get('message', '')}")
            output.append(f"   💡 {opp.get('suggestion', '')}")
            if opp.get("benefit"):
                output.append(f"   ✅ {opp['benefit']}")
            output.append("")

    # Build performance
    build_perf = analysis.get("build_time_analysis", {})
    if build_perf:
        complexity = build_perf.get("source_complexity", {})
        output.append(f"🏗️ **Build Complexity:** {complexity.get('complexity', 'unknown')}")
        output.append(f"- Files: {complexity.get('file_count', 0)}")

        dep_impact = build_perf.get("dependency_impact", {})
        impact = dep_impact.get("impact", "unknown")
        output.append(f"📦 **Dependency Impact:** {impact}")

        heavy_deps = dep_impact.get("heavy_dependencies", [])
        if heavy_deps:
            output.append(f"- Heavy dependencies: {', '.join(heavy_deps)}")
        output.append("")

    # Target analysis
    targets = analysis.get("target_analysis", {})
    if targets:
        target_list = targets.get("targets", [])
        output.append(f"🎯 **Compilation Targets:** {len(target_list)}")
        for target in target_list[:5]:
            output.append(f"- {target['type']}: {target['name']}")
        output.append("")

    return '\n'.join(output)