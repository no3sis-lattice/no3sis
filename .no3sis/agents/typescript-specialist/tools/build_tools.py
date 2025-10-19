"""
TypeScript Build Optimization Tools

Tools for optimizing build configuration, analyzing bundle size,
and suggesting performance improvements for TypeScript/JavaScript projects.
"""

import json
import re
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional


async def optimize_build_config(config_path: str, build_tool: str = "vite") -> Dict[str, Any]:
    """
    Optimize build configuration for better performance.

    Args:
        config_path: Path to build configuration file
        build_tool: Build tool (vite, webpack, esbuild, rollup)

    Returns:
        Dict with build optimization suggestions
    """
    try:
        path = Path(config_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Configuration file not found: {config_path}"
                }],
                "success": False,
                "error": "config_not_found"
            }

        content = path.read_text(encoding='utf-8')

        analysis = await _analyze_build_config(content, str(path), build_tool)

        formatted_output = _format_build_optimization_results(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "config_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Build config optimization failed for {config_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def analyze_bundle_size(project_path: str) -> Dict[str, Any]:
    """
    Analyze and optimize bundle size for the project.

    Args:
        project_path: Path to project directory

    Returns:
        Dict with bundle size analysis and optimization suggestions
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

        analysis = await _analyze_project_bundle(str(path))

        formatted_output = _format_bundle_analysis_results(analysis)

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
                "text": f"❌ Bundle size analysis failed for {project_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _analyze_build_config(content: str, config_path: str, build_tool: str) -> Dict[str, Any]:
    """Analyze build configuration for optimization opportunities."""

    config_analysis = {
        "build_tool": build_tool,
        "current_config": _parse_config_content(content, build_tool),
        "optimizations": [],
        "performance_suggestions": [],
        "security_suggestions": []
    }

    # Tool-specific analysis
    if build_tool == "vite":
        config_analysis.update(await _analyze_vite_config(content))
    elif build_tool == "webpack":
        config_analysis.update(await _analyze_webpack_config(content))
    elif build_tool == "esbuild":
        config_analysis.update(await _analyze_esbuild_config(content))
    elif build_tool == "rollup":
        config_analysis.update(await _analyze_rollup_config(content))

    # General optimizations
    config_analysis["optimizations"].extend(_suggest_general_optimizations(content, build_tool))

    return config_analysis


def _parse_config_content(content: str, build_tool: str) -> Dict[str, Any]:
    """Parse configuration content based on build tool."""
    config = {"raw_content": content}

    try:
        # Try to extract JavaScript object/JSON-like content
        if content.strip().startswith('{') and content.strip().endswith('}'):
            # JSON-like config
            config["type"] = "json"
        elif "export default" in content or "module.exports" in content:
            # JavaScript config
            config["type"] = "javascript"
        else:
            config["type"] = "unknown"

        # Extract key configurations
        config["has_typescript"] = "typescript" in content.lower() or ".ts" in content
        config["has_minification"] = any(keyword in content.lower() for keyword in ["minify", "uglify", "terser"])
        config["has_tree_shaking"] = "treeshake" in content.lower() or "sideEffects" in content
        config["has_code_splitting"] = any(keyword in content.lower() for keyword in ["split", "chunk"])
        config["has_compression"] = any(keyword in content.lower() for keyword in ["gzip", "brotli", "compress"])

    except Exception:
        config["type"] = "error"

    return config


async def _analyze_vite_config(content: str) -> Dict[str, Any]:
    """Analyze Vite configuration."""
    analysis = {
        "vite_features": {
            "hmr": "hmr" in content.lower() or "hot" in content.lower(),
            "dev_server": "server" in content,
            "build_options": "build" in content,
            "plugins": "plugins" in content,
            "resolve_alias": "alias" in content
        }
    }

    optimizations = []

    # Check for common optimizations
    if "rollupOptions" not in content:
        optimizations.append({
            "type": "rollup_options",
            "priority": "medium",
            "message": "Add rollupOptions for advanced bundle optimization",
            "suggestion": "Configure input, output, and external dependencies",
            "code": """build: {
  rollupOptions: {
    output: {
      manualChunks: {
        vendor: ['react', 'react-dom'],
        utils: ['lodash']
      }
    }
  }
}"""
        })

    if "chunkSizeWarningLimit" not in content:
        optimizations.append({
            "type": "chunk_size",
            "priority": "low",
            "message": "Set chunk size warning limit",
            "suggestion": "Configure appropriate chunk size limits",
            "code": "build: { chunkSizeWarningLimit: 1000 }"
        })

    # Check for missing plugins
    common_plugins = ["@vitejs/plugin-react", "@vitejs/plugin-typescript"]
    missing_plugins = []
    for plugin in common_plugins:
        if plugin not in content:
            missing_plugins.append(plugin)

    if missing_plugins:
        optimizations.append({
            "type": "missing_plugins",
            "priority": "medium",
            "message": f"Consider adding common plugins: {', '.join(missing_plugins)}",
            "suggestion": "Add plugins for better development experience"
        })

    analysis["optimizations"] = optimizations
    return analysis


async def _analyze_webpack_config(content: str) -> Dict[str, Any]:
    """Analyze Webpack configuration."""
    analysis = {
        "webpack_features": {
            "mode": "mode:" in content or "mode =" in content,
            "entry": "entry:" in content or "entry =" in content,
            "output": "output:" in content or "output =" in content,
            "optimization": "optimization:" in content,
            "plugins": "plugins:" in content,
            "module_rules": "module:" in content and "rules:" in content
        }
    }

    optimizations = []

    # Check for optimization settings
    if "optimization" not in content:
        optimizations.append({
            "type": "optimization_missing",
            "priority": "high",
            "message": "Add optimization configuration",
            "suggestion": "Configure splitChunks, minimize, and usedExports",
            "code": """optimization: {
  splitChunks: {
    chunks: 'all',
    cacheGroups: {
      vendor: {
        test: /[\\/]node_modules[\\/]/,
        name: 'vendors',
        chunks: 'all'
      }
    }
  },
  usedExports: true,
  minimize: true
}"""
        })

    if "splitChunks" not in content:
        optimizations.append({
            "type": "code_splitting",
            "priority": "medium",
            "message": "Enable code splitting for better caching",
            "suggestion": "Configure splitChunks for vendor and common code separation"
        })

    if "TerserPlugin" not in content and "minimize" not in content:
        optimizations.append({
            "type": "minification",
            "priority": "medium",
            "message": "Add minification for production builds",
            "suggestion": "Configure TerserPlugin or enable minimize option"
        })

    analysis["optimizations"] = optimizations
    return analysis


async def _analyze_esbuild_config(content: str) -> Dict[str, Any]:
    """Analyze esbuild configuration."""
    analysis = {
        "esbuild_features": {
            "minify": "minify" in content,
            "tree_shaking": "treeShaking" in content,
            "bundle": "bundle" in content,
            "target": "target" in content,
            "format": "format" in content
        }
    }

    optimizations = []

    if "minify: true" not in content:
        optimizations.append({
            "type": "minification",
            "priority": "high",
            "message": "Enable minification for production",
            "suggestion": "Set minify: true for smaller bundles"
        })

    if "treeShaking" not in content:
        optimizations.append({
            "type": "tree_shaking",
            "priority": "medium",
            "message": "Enable tree shaking",
            "suggestion": "Add treeShaking: true to remove unused code"
        })

    if "target:" not in content:
        optimizations.append({
            "type": "target_missing",
            "priority": "low",
            "message": "Specify target environment",
            "suggestion": "Set target to optimize for specific browsers/Node.js versions"
        })

    analysis["optimizations"] = optimizations
    return analysis


async def _analyze_rollup_config(content: str) -> Dict[str, Any]:
    """Analyze Rollup configuration."""
    analysis = {
        "rollup_features": {
            "input": "input:" in content,
            "output": "output:" in content,
            "plugins": "plugins:" in content,
            "external": "external:" in content,
            "tree_shake": "treeshake" in content.lower()
        }
    }

    optimizations = []

    if "treeshake" not in content.lower():
        optimizations.append({
            "type": "tree_shaking",
            "priority": "high",
            "message": "Enable tree shaking",
            "suggestion": "Add treeshake: true for dead code elimination"
        })

    if "external:" not in content:
        optimizations.append({
            "type": "externals",
            "priority": "medium",
            "message": "Configure external dependencies",
            "suggestion": "Mark large libraries as external to reduce bundle size"
        })

    analysis["optimizations"] = optimizations
    return analysis


def _suggest_general_optimizations(content: str, build_tool: str) -> List[Dict[str, Any]]:
    """Suggest general build optimizations."""
    optimizations = []

    # Check for development vs production configurations
    if "NODE_ENV" not in content and "process.env" not in content:
        optimizations.append({
            "type": "environment_config",
            "priority": "medium",
            "message": "Add environment-specific configurations",
            "suggestion": "Use different settings for development and production",
            "benefit": "Optimized builds for each environment"
        })

    # Check for source maps configuration
    if "sourcemap" not in content.lower() and "devtool" not in content:
        optimizations.append({
            "type": "source_maps",
            "priority": "low",
            "message": "Configure source maps for debugging",
            "suggestion": "Enable source maps for development, optimize for production",
            "benefit": "Better debugging experience"
        })

    # Check for asset optimization
    if "asset" not in content.lower() and "static" not in content.lower():
        optimizations.append({
            "type": "asset_optimization",
            "priority": "medium",
            "message": "Configure asset optimization",
            "suggestion": "Set up image optimization, compression, and caching",
            "benefit": "Smaller bundle sizes and faster loading"
        })

    return optimizations


async def _analyze_project_bundle(project_path: str) -> Dict[str, Any]:
    """Analyze project bundle size and dependencies."""
    path = Path(project_path)

    analysis = {
        "project_info": await _get_project_info(path),
        "dependencies": await _analyze_dependencies(path),
        "bundle_estimate": await _estimate_bundle_size(path),
        "optimization_opportunities": []
    }

    # Generate optimization suggestions
    analysis["optimization_opportunities"] = _generate_bundle_optimizations(
        analysis["dependencies"],
        analysis["bundle_estimate"]
    )

    return analysis


async def _get_project_info(path: Path) -> Dict[str, Any]:
    """Get basic project information."""
    package_json = path / "package.json"
    info = {
        "has_package_json": package_json.exists(),
        "build_tools": [],
        "frameworks": []
    }

    if package_json.exists():
        try:
            pkg_data = json.loads(package_json.read_text())
            all_deps = {
                **pkg_data.get("dependencies", {}),
                **pkg_data.get("devDependencies", {})
            }

            # Detect build tools
            build_tools = ["vite", "webpack", "esbuild", "rollup", "parcel"]
            for tool in build_tools:
                if tool in all_deps or f"@{tool}" in all_deps:
                    info["build_tools"].append(tool)

            # Detect frameworks
            frameworks = ["react", "vue", "angular", "svelte"]
            for framework in frameworks:
                if framework in all_deps or f"@{framework}" in all_deps:
                    info["frameworks"].append(framework)

            info["scripts"] = pkg_data.get("scripts", {})

        except Exception:
            pass

    return info


async def _analyze_dependencies(path: Path) -> Dict[str, Any]:
    """Analyze project dependencies for size impact."""
    package_json = path / "package.json"
    deps_analysis = {
        "total_dependencies": 0,
        "large_dependencies": [],
        "duplicate_dependencies": [],
        "unused_dependencies": []
    }

    if not package_json.exists():
        return deps_analysis

    try:
        pkg_data = json.loads(package_json.read_text())
        dependencies = pkg_data.get("dependencies", {})
        dev_dependencies = pkg_data.get("devDependencies", {})

        deps_analysis["total_dependencies"] = len(dependencies) + len(dev_dependencies)

        # Check for commonly large dependencies
        large_deps = [
            "moment", "lodash", "antd", "@material-ui/core", "material-ui",
            "rxjs", "d3", "chart.js", "three", "tensorflow"
        ]

        for dep in large_deps:
            if dep in dependencies:
                deps_analysis["large_dependencies"].append({
                    "name": dep,
                    "suggestion": _get_lightweight_alternative(dep)
                })

        # Check for potential duplicates (simplified)
        all_deps = list(dependencies.keys()) + list(dev_dependencies.keys())
        potential_duplicates = []
        for i, dep1 in enumerate(all_deps):
            for dep2 in all_deps[i+1:]:
                if _are_similar_packages(dep1, dep2):
                    potential_duplicates.append((dep1, dep2))

        deps_analysis["duplicate_dependencies"] = potential_duplicates[:5]  # Limit to first 5

    except Exception:
        pass

    return deps_analysis


def _get_lightweight_alternative(package_name: str) -> str:
    """Get lightweight alternatives for common packages."""
    alternatives = {
        "moment": "date-fns or dayjs (90% smaller)",
        "lodash": "Individual lodash functions or native ES6",
        "antd": "Selective imports or lighter UI library",
        "@material-ui/core": "@mui/material with tree shaking",
        "rxjs": "Individual operators import",
        "chart.js": "Lightweight charting library like recharts"
    }
    return alternatives.get(package_name, "Consider lighter alternatives")


def _are_similar_packages(pkg1: str, pkg2: str) -> bool:
    """Check if two packages might be duplicates or similar."""
    # Simple similarity check
    similarity_patterns = [
        ("react", "preact"),
        ("jquery", "$"),
        ("typescript", "ts-"),
        ("webpack", "rollup"),
        ("jest", "vitest")
    ]

    for pattern1, pattern2 in similarity_patterns:
        if (pattern1 in pkg1.lower() and pattern2 in pkg2.lower()) or \
           (pattern2 in pkg1.lower() and pattern1 in pkg2.lower()):
            return True

    return False


async def _estimate_bundle_size(path: Path) -> Dict[str, Any]:
    """Estimate bundle size based on dependencies and source code."""
    estimate = {
        "source_size_kb": 0,
        "estimated_bundle_kb": 0,
        "large_files": []
    }

    # Analyze source files
    source_files = list(path.glob('**/*.{js,jsx,ts,tsx}'))
    source_files = [f for f in source_files if not any(exclude in str(f) for exclude in ['node_modules', '.git', 'dist', 'build'])]

    total_size = 0
    large_files = []

    for file in source_files:
        try:
            size = file.stat().st_size
            total_size += size

            if size > 50000:  # Files larger than 50KB
                large_files.append({
                    "file": str(file.relative_to(path)),
                    "size_kb": round(size / 1024, 1)
                })

        except Exception:
            continue

    estimate["source_size_kb"] = round(total_size / 1024, 1)
    estimate["large_files"] = sorted(large_files, key=lambda x: x["size_kb"], reverse=True)[:10]

    # Rough bundle size estimation (source + dependencies)
    # This is a very rough estimate
    estimate["estimated_bundle_kb"] = estimate["source_size_kb"] * 3  # Rough multiplier for bundled size

    return estimate


def _generate_bundle_optimizations(dependencies: Dict, bundle_estimate: Dict) -> List[Dict[str, Any]]:
    """Generate bundle optimization recommendations."""
    optimizations = []

    # Large dependency recommendations
    large_deps = dependencies.get("large_dependencies", [])
    if large_deps:
        optimizations.append({
            "type": "dependency_optimization",
            "priority": "high",
            "message": f"Replace large dependencies: {', '.join([d['name'] for d in large_deps[:3]])}",
            "suggestions": [f"{d['name']}: {d['suggestion']}" for d in large_deps[:3]],
            "impact": "30-70% bundle size reduction"
        })

    # Duplicate dependencies
    duplicates = dependencies.get("duplicate_dependencies", [])
    if duplicates:
        optimizations.append({
            "type": "duplicate_removal",
            "priority": "medium",
            "message": f"Remove duplicate dependencies: {len(duplicates)} potential duplicates found",
            "suggestion": "Consolidate similar packages and remove unused ones",
            "impact": "10-20% bundle size reduction"
        })

    # Large files
    large_files = bundle_estimate.get("large_files", [])
    if large_files:
        optimizations.append({
            "type": "code_splitting",
            "priority": "medium",
            "message": f"Split large files: {len(large_files)} files > 50KB",
            "suggestion": "Implement code splitting and lazy loading for large components",
            "files": [f["file"] for f in large_files[:5]],
            "impact": "Improved loading performance"
        })

    # Bundle size warning
    estimated_size = bundle_estimate.get("estimated_bundle_kb", 0)
    if estimated_size > 1000:  # > 1MB
        optimizations.append({
            "type": "bundle_size_warning",
            "priority": "high",
            "message": f"Large bundle size: ~{estimated_size}KB estimated",
            "suggestion": "Implement tree shaking, code splitting, and dependency optimization",
            "impact": "Significant performance improvement"
        })

    # Tree shaking recommendation
    optimizations.append({
        "type": "tree_shaking",
        "priority": "medium",
        "message": "Enable tree shaking to remove unused code",
        "suggestion": "Configure your bundler to eliminate dead code",
        "impact": "10-30% size reduction"
    })

    return optimizations


def _format_build_optimization_results(analysis: Dict[str, Any]) -> str:
    """Format build optimization results."""
    output = []

    build_tool = analysis.get("build_tool", "unknown")
    output.append(f"⚙️ **Build Configuration Optimization ({build_tool.title()})**\n")

    # Current config overview
    current_config = analysis.get("current_config", {})
    config_type = current_config.get("type", "unknown")
    output.append(f"📄 **Configuration Type:** {config_type}")

    features = []
    if current_config.get("has_typescript"):
        features.append("TypeScript ✅")
    if current_config.get("has_minification"):
        features.append("Minification ✅")
    if current_config.get("has_tree_shaking"):
        features.append("Tree Shaking ✅")
    if current_config.get("has_code_splitting"):
        features.append("Code Splitting ✅")
    if current_config.get("has_compression"):
        features.append("Compression ✅")

    if features:
        output.append(f"📦 **Current Features:** {', '.join(features)}")
    output.append("")

    # Tool-specific features (for Vite, Webpack, etc.)
    if build_tool == "vite" and "vite_features" in analysis:
        vite_features = analysis["vite_features"]
        output.append("🚀 **Vite Features:**")
        for feature, enabled in vite_features.items():
            status = "✅" if enabled else "❌"
            output.append(f"- {feature.replace('_', ' ').title()}: {status}")
        output.append("")

    # Optimizations
    optimizations = analysis.get("optimizations", [])
    if optimizations:
        output.append("💡 **Optimization Suggestions:**")
        for opt in optimizations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(opt.get("priority"), "⚪")
            message = opt.get("message", "")
            suggestion = opt.get("suggestion", "")

            output.append(f"{priority_emoji} {message}")
            if suggestion:
                output.append(f"   💡 {suggestion}")

            if opt.get("code"):
                output.append(f"   📝 Example:")
                output.append(f"   ```javascript\n   {opt['code']}\n   ```")
            output.append("")

    # Performance suggestions
    perf_suggestions = analysis.get("performance_suggestions", [])
    if perf_suggestions:
        output.append("⚡ **Performance Suggestions:**")
        for suggestion in perf_suggestions:
            output.append(f"- {suggestion}")
        output.append("")

    # Security suggestions
    security_suggestions = analysis.get("security_suggestions", [])
    if security_suggestions:
        output.append("🔒 **Security Suggestions:**")
        for suggestion in security_suggestions:
            output.append(f"- {suggestion}")
        output.append("")

    if not optimizations and not perf_suggestions and not security_suggestions:
        output.append("✅ **Configuration looks well optimized!**")

    return '\n'.join(output)


def _format_bundle_analysis_results(analysis: Dict[str, Any]) -> str:
    """Format bundle analysis results."""
    output = []

    output.append("📦 **Bundle Size Analysis**\n")

    # Project info
    project_info = analysis.get("project_info", {})
    output.append("📋 **Project Overview:**")

    build_tools = project_info.get("build_tools", [])
    if build_tools:
        output.append(f"- Build tools: {', '.join(build_tools)}")

    frameworks = project_info.get("frameworks", [])
    if frameworks:
        output.append(f"- Frameworks: {', '.join(frameworks)}")

    scripts = project_info.get("scripts", {})
    build_scripts = [k for k in scripts.keys() if 'build' in k]
    if build_scripts:
        output.append(f"- Build scripts: {', '.join(build_scripts)}")
    output.append("")

    # Dependencies analysis
    deps = analysis.get("dependencies", {})
    total_deps = deps.get("total_dependencies", 0)
    output.append(f"📚 **Dependencies:** {total_deps} total")

    large_deps = deps.get("large_dependencies", [])
    if large_deps:
        output.append("⚠️ **Large Dependencies Found:**")
        for dep in large_deps:
            output.append(f"- {dep['name']}: {dep['suggestion']}")
        output.append("")

    duplicates = deps.get("duplicate_dependencies", [])
    if duplicates:
        output.append(f"🔄 **Potential Duplicates:** {len(duplicates)} found")
        for dup1, dup2 in duplicates[:3]:
            output.append(f"- {dup1} / {dup2}")
        output.append("")

    # Bundle size estimate
    bundle = analysis.get("bundle_estimate", {})
    source_size = bundle.get("source_size_kb", 0)
    estimated_size = bundle.get("estimated_bundle_kb", 0)

    output.append("📊 **Size Analysis:**")
    output.append(f"- Source code: {source_size} KB")
    output.append(f"- Estimated bundle: {estimated_size} KB")

    if estimated_size > 1000:
        output.append("🔴 **Warning:** Large bundle size detected")
    elif estimated_size > 500:
        output.append("🟡 **Notice:** Consider optimization for better performance")
    else:
        output.append("✅ **Good:** Bundle size is reasonable")
    output.append("")

    # Large files
    large_files = bundle.get("large_files", [])
    if large_files:
        output.append("📁 **Large Files (>50KB):**")
        for file in large_files[:5]:
            output.append(f"- {file['file']}: {file['size_kb']} KB")
        if len(large_files) > 5:
            output.append(f"- ... and {len(large_files) - 5} more")
        output.append("")

    # Optimization opportunities
    optimizations = analysis.get("optimization_opportunities", [])
    if optimizations:
        output.append("💡 **Optimization Opportunities:**")
        for opt in optimizations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(opt.get("priority"), "⚪")
            message = opt.get("message", "")
            suggestion = opt.get("suggestion", "")
            impact = opt.get("impact", "")

            output.append(f"{priority_emoji} **{message}**")
            if suggestion:
                output.append(f"   💡 {suggestion}")
            if impact:
                output.append(f"   📈 Impact: {impact}")

            suggestions = opt.get("suggestions", [])
            if suggestions:
                for sugg in suggestions[:3]:
                    output.append(f"   - {sugg}")

            files = opt.get("files", [])
            if files:
                output.append(f"   📄 Files: {', '.join(files[:3])}")
                if len(files) > 3:
                    output.append(f"   ... and {len(files) - 3} more")
            output.append("")

    # Action items
    output.append("🎯 **Recommended Actions:**")
    output.append("1. Enable tree shaking in your bundler configuration")
    output.append("2. Implement code splitting for large components")
    output.append("3. Consider lighter alternatives for large dependencies")
    output.append("4. Enable compression (gzip/brotli) on your server")
    output.append("5. Use dynamic imports for non-critical code")

    return '\n'.join(output)