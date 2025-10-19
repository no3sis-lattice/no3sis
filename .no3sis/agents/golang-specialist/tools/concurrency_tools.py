"""
Go Concurrency Analysis Tools

Specialized tools for analyzing Go concurrency patterns including goroutines,
channels, select statements, and synchronization primitives.
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Optional, Set, Tuple


def analyze_goroutines(file_path: str, check_leaks: bool, config: Dict[str, Any]) -> str:
    """
    Analyze goroutine usage patterns and potential issues.

    Args:
        file_path: Path to the Go file containing goroutines
        check_leaks: Whether to check for potential goroutine leaks
        config: Agent configuration

    Returns:
        Detailed goroutine analysis report
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        analysis = {
            "file_path": file_path,
            "goroutine_patterns": [],
            "potential_issues": [],
            "recommendations": []
        }

        # Find all goroutine launches
        goroutine_patterns = _find_goroutine_patterns(content)
        analysis["goroutine_patterns"] = goroutine_patterns

        # Check for common issues
        if check_leaks:
            leak_issues = _check_goroutine_leaks(content, config)
            analysis["potential_issues"].extend(leak_issues)

        # Check synchronization patterns
        sync_issues = _check_synchronization_patterns(content, config)
        analysis["potential_issues"].extend(sync_issues)

        # Generate recommendations
        recommendations = _generate_goroutine_recommendations(content, goroutine_patterns, config)
        analysis["recommendations"] = recommendations

        return _format_goroutine_report(analysis, config)

    except Exception as e:
        return f"❌ Goroutine analysis failed: {str(e)}"


def check_channel_patterns(file_path: str, pattern_type: str, config: Dict[str, Any]) -> str:
    """
    Analyze channel usage patterns and detect common anti-patterns.

    Args:
        file_path: Path to the Go file with channel usage
        pattern_type: Type of patterns to check (buffered, unbuffered, select, all)
        config: Agent configuration

    Returns:
        Channel pattern analysis report
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        analysis = {
            "file_path": file_path,
            "pattern_type": pattern_type,
            "channel_declarations": [],
            "channel_operations": [],
            "select_statements": [],
            "issues": []
        }

        # Find channel declarations
        if pattern_type in ["buffered", "unbuffered", "all"]:
            channels = _find_channel_declarations(content)
            analysis["channel_declarations"] = channels

        # Find channel operations
        operations = _find_channel_operations(content)
        analysis["channel_operations"] = operations

        # Find select statements
        if pattern_type in ["select", "all"]:
            selects = _find_select_statements(content)
            analysis["select_statements"] = selects

        # Check for anti-patterns
        issues = _check_channel_antipatterns(content, pattern_type, config)
        analysis["issues"] = issues

        return _format_channel_report(analysis, config)

    except Exception as e:
        return f"❌ Channel analysis failed: {str(e)}"


def detect_race_conditions(directory: str, include_tests: bool, config: Dict[str, Any]) -> str:
    """
    Detect potential race conditions in Go code using static analysis.

    Args:
        directory: Directory to scan for race conditions
        include_tests: Whether to include test files in analysis
        config: Agent configuration

    Returns:
        Race condition detection report
    """
    try:
        if not os.path.exists(directory):
            return f"❌ Directory not found: {directory}"

        race_analysis = {
            "directory": directory,
            "files_analyzed": 0,
            "potential_races": [],
            "shared_variables": [],
            "unsafe_patterns": []
        }

        # Find Go files
        go_files = _find_go_files(directory, include_tests)
        race_analysis["files_analyzed"] = len(go_files)

        # Analyze each file
        for file_path in go_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()

                # Check for shared variable access
                shared_vars = _find_shared_variable_access(content, file_path)
                race_analysis["shared_variables"].extend(shared_vars)

                # Check for unsafe patterns
                unsafe_patterns = _find_unsafe_patterns(content, file_path)
                race_analysis["unsafe_patterns"].extend(unsafe_patterns)

                # Check for potential races
                races = _detect_potential_races(content, file_path, config)
                race_analysis["potential_races"].extend(races)

            except Exception as e:
                print(f"⚠️ Error analyzing {file_path}: {e}")

        # Try to run go race detector if available
        race_detector_output = _run_race_detector(directory, config)
        if race_detector_output:
            race_analysis["race_detector_output"] = race_detector_output

        return _format_race_detection_report(race_analysis, config)

    except Exception as e:
        return f"❌ Race condition detection failed: {str(e)}"


def _find_goroutine_patterns(content: str) -> List[Dict[str, Any]]:
    """Find goroutine launch patterns in the code."""
    patterns = []

    # Find 'go' statements
    go_pattern = r'go\s+(\w+(?:\([^)]*\))?|\([^)]*\)\s*\{[^}]*\})'
    matches = re.finditer(go_pattern, content)

    for match in matches:
        line_num = content[:match.start()].count('\n') + 1
        goroutine_call = match.group(1).strip()

        pattern_type = "function_call"
        if goroutine_call.startswith('(') or '{' in goroutine_call:
            pattern_type = "anonymous_function"

        patterns.append({
            "line": line_num,
            "call": goroutine_call,
            "type": pattern_type,
            "full_match": match.group(0)
        })

    return patterns


def _check_goroutine_leaks(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check for potential goroutine leaks."""
    issues = []

    # Check for goroutines without proper termination
    if 'for {' in content or 'for;;' in content:
        line_num = content.find('for {')
        if line_num != -1:
            line_num = content[:line_num].count('\n') + 1
            issues.append({
                "type": "infinite_loop",
                "severity": "warning",
                "line": line_num,
                "message": "Infinite loop detected - ensure goroutine has termination condition",
                "suggestion": "Add context cancellation or break condition"
            })

    # Check for missing channel close in producers
    channel_sends = re.findall(r'(\w+)\s*<-', content)
    for channel in channel_sends:
        if f'close({channel})' not in content:
            issues.append({
                "type": "unclosed_channel",
                "severity": "info",
                "message": f"Channel '{channel}' may not be properly closed",
                "suggestion": "Ensure channels are closed when done sending"
            })

    return issues


def _check_synchronization_patterns(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check synchronization patterns for common issues."""
    issues = []

    # Check for mutex usage
    if 'sync.Mutex' in content or 'sync.RWMutex' in content:
        # Check for defer usage with locks
        lock_pattern = r'(\w+)\.Lock\(\)'
        locks = re.findall(lock_pattern, content)

        for lock_var in locks:
            if f'defer {lock_var}.Unlock()' not in content:
                issues.append({
                    "type": "missing_defer_unlock",
                    "severity": "error",
                    "message": f"Missing defer {lock_var}.Unlock() after Lock()",
                    "suggestion": f"Add 'defer {lock_var}.Unlock()' immediately after Lock()"
                })

    # Check for WaitGroup usage
    if 'sync.WaitGroup' in content:
        if '.Add(' in content and '.Done()' not in content:
            issues.append({
                "type": "missing_waitgroup_done",
                "severity": "error",
                "message": "WaitGroup.Add() called but no corresponding Done()",
                "suggestion": "Ensure every Add() has a corresponding Done(), preferably in defer"
            })

    return issues


def _generate_goroutine_recommendations(content: str, patterns: List[Dict[str, Any]], config: Dict[str, Any]) -> List[str]:
    """Generate recommendations for goroutine usage."""
    recommendations = []

    if len(patterns) > 5:
        recommendations.append(
            "Consider using a worker pool pattern to limit concurrent goroutines"
        )

    if any(p['type'] == 'anonymous_function' for p in patterns):
        recommendations.append(
            "Consider extracting anonymous goroutine functions for better testing and reusability"
        )

    if 'context' not in content and patterns:
        recommendations.append(
            "Consider using context.Context for graceful goroutine cancellation"
        )

    return recommendations


def _find_channel_declarations(content: str) -> List[Dict[str, Any]]:
    """Find channel declarations and their types."""
    channels = []

    # Find make(chan ...) patterns
    make_pattern = r'make\(chan\s+(\w+)(?:,\s*(\d+))?\)'
    matches = re.finditer(make_pattern, content)

    for match in matches:
        line_num = content[:match.start()].count('\n') + 1
        channel_type = match.group(1)
        buffer_size = match.group(2)

        channels.append({
            "line": line_num,
            "type": channel_type,
            "buffer_size": int(buffer_size) if buffer_size else 0,
            "is_buffered": bool(buffer_size)
        })

    # Find chan type declarations
    chan_pattern = r'chan\s+(\w+)'
    matches = re.finditer(chan_pattern, content)

    for match in matches:
        if 'make(' not in content[max(0, match.start()-20):match.end()+20]:
            line_num = content[:match.start()].count('\n') + 1
            channels.append({
                "line": line_num,
                "type": match.group(1),
                "buffer_size": None,
                "is_buffered": None
            })

    return channels


def _find_channel_operations(content: str) -> List[Dict[str, Any]]:
    """Find channel send and receive operations."""
    operations = []

    # Find channel sends (ch <- value)
    send_pattern = r'(\w+)\s*<-\s*([^;]+)'
    sends = re.finditer(send_pattern, content)

    for send in sends:
        line_num = content[:send.start()].count('\n') + 1
        operations.append({
            "line": line_num,
            "type": "send",
            "channel": send.group(1),
            "value": send.group(2).strip()
        })

    # Find channel receives (<-ch or val := <-ch)
    recv_pattern = r'(?:(\w+)\s*:?=\s*)?<-\s*(\w+)'
    receives = re.finditer(recv_pattern, content)

    for recv in receives:
        line_num = content[:recv.start()].count('\n') + 1
        operations.append({
            "line": line_num,
            "type": "receive",
            "channel": recv.group(2),
            "variable": recv.group(1) if recv.group(1) else None
        })

    return operations


def _find_select_statements(content: str) -> List[Dict[str, Any]]:
    """Find and analyze select statements."""
    selects = []

    select_pattern = r'select\s*\{'
    matches = re.finditer(select_pattern, content)

    for match in matches:
        line_num = content[:match.start()].count('\n') + 1

        # Find the end of this select block
        select_start = match.end()
        brace_count = 1
        select_end = select_start

        for i, char in enumerate(content[select_start:]):
            if char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
                if brace_count == 0:
                    select_end = select_start + i
                    break

        select_body = content[select_start:select_end]

        # Count cases
        case_count = len(re.findall(r'case\s+', select_body))
        has_default = 'default:' in select_body

        selects.append({
            "line": line_num,
            "case_count": case_count,
            "has_default": has_default,
            "body_lines": len(select_body.splitlines())
        })

    return selects


def _check_channel_antipatterns(content: str, pattern_type: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check for common channel anti-patterns."""
    issues = []

    # Check for unbuffered channel deadlocks
    if 'make(chan' in content and '<-' in content:
        # Simple heuristic: unbuffered channel with immediate send/receive
        lines = content.splitlines()
        for i, line in enumerate(lines):
            if 'make(chan' in line and ',0)' not in line and ',' not in line:
                # Check next few lines for immediate operations
                for j in range(i+1, min(i+5, len(lines))):
                    if '<-' in lines[j] and 'go' not in lines[j]:
                        issues.append({
                            "type": "potential_deadlock",
                            "severity": "warning",
                            "line": i+1,
                            "message": "Potential deadlock with unbuffered channel",
                            "suggestion": "Use buffered channel or separate goroutine"
                        })
                        break

    # Check for channel leaks (sends without receives)
    send_channels = set(re.findall(r'(\w+)\s*<-', content))
    recv_channels = set(re.findall(r'<-\s*(\w+)', content))

    for channel in send_channels:
        if channel not in recv_channels and f'close({channel})' not in content:
            issues.append({
                "type": "channel_leak",
                "severity": "warning",
                "message": f"Channel '{channel}' has sends but no receives",
                "suggestion": "Ensure channels have corresponding receivers or are properly closed"
            })

    return issues


def _find_go_files(directory: str, include_tests: bool) -> List[str]:
    """Find all Go files in the directory."""
    go_files = []
    path = Path(directory)

    for file_path in path.rglob("*.go"):
        if not include_tests and file_path.name.endswith('_test.go'):
            continue
        go_files.append(str(file_path))

    return go_files


def _find_shared_variable_access(content: str, file_path: str) -> List[Dict[str, Any]]:
    """Find potential shared variable access patterns."""
    shared_vars = []

    # Look for global variables
    global_var_pattern = r'^var\s+(\w+)'
    matches = re.finditer(global_var_pattern, content, re.MULTILINE)

    for match in matches:
        var_name = match.group(1)
        line_num = content[:match.start()].count('\n') + 1

        # Check if this variable is accessed in goroutines
        goroutine_accesses = []
        lines = content.splitlines()

        in_goroutine = False
        goroutine_line = 0

        for i, line in enumerate(lines, 1):
            if 'go ' in line and '{' in line:
                in_goroutine = True
                goroutine_line = i
            elif in_goroutine and '}' in line:
                in_goroutine = False

            if in_goroutine and var_name in line:
                goroutine_accesses.append({
                    "line": i,
                    "goroutine_start": goroutine_line
                })

        if goroutine_accesses:
            shared_vars.append({
                "file": file_path,
                "variable": var_name,
                "declaration_line": line_num,
                "goroutine_accesses": goroutine_accesses
            })

    return shared_vars


def _find_unsafe_patterns(content: str, file_path: str) -> List[Dict[str, Any]]:
    """Find unsafe concurrency patterns."""
    patterns = []

    # Check for map concurrent access without sync
    if 'map[' in content and 'sync.Mutex' not in content and 'sync.RWMutex' not in content:
        if 'go ' in content:  # Has goroutines
            patterns.append({
                "file": file_path,
                "type": "unsynchronized_map",
                "severity": "error",
                "message": "Map access in concurrent context without synchronization",
                "suggestion": "Use sync.Mutex/RWMutex or sync.Map for concurrent access"
            })

    # Check for slice concurrent modification
    if 'append(' in content and 'go ' in content and 'sync.Mutex' not in content:
        patterns.append({
            "file": file_path,
            "type": "unsynchronized_slice",
            "severity": "warning",
            "message": "Slice modification in concurrent context",
            "suggestion": "Consider using synchronization for slice modifications"
        })

    return patterns


def _detect_potential_races(content: str, file_path: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Detect potential race conditions using pattern analysis."""
    races = []

    # Simple heuristic: shared resource access without synchronization
    lines = content.splitlines()
    has_goroutines = any('go ' in line for line in lines)

    if has_goroutines:
        # Look for variable modifications
        for i, line in enumerate(lines, 1):
            # Assignment operations
            if '=' in line and not line.strip().startswith('//'):
                if any(keyword not in line for keyword in ['sync.', 'atomic.', 'chan']):
                    # Check if this variable is used in multiple places
                    var_match = re.search(r'(\w+)\s*[=:]', line)
                    if var_match:
                        var_name = var_match.group(1)
                        var_usages = sum(1 for l in lines if var_name in l)

                        if var_usages > 2:  # Variable used in multiple places
                            races.append({
                                "file": file_path,
                                "line": i,
                                "variable": var_name,
                                "type": "unsynchronized_write",
                                "severity": "warning",
                                "message": f"Potential race on variable '{var_name}'"
                            })

    return races


def _run_race_detector(directory: str, config: Dict[str, Any]) -> Optional[str]:
    """Run Go race detector if available."""
    try:
        # Try to build with race detector
        result = subprocess.run(
            ['go', 'build', '-race', './...'],
            cwd=directory,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0:
            return "✅ Race detector build passed"
        else:
            return f"⚠️ Race detector found issues:\n{result.stderr}"

    except (subprocess.TimeoutExpired, FileNotFoundError, subprocess.CalledProcessError):
        return None


def _format_goroutine_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the goroutine analysis report."""
    report = "# Goroutine Analysis Report\n\n"
    report += f"**File:** `{analysis['file_path']}`\n\n"

    # Goroutine patterns
    patterns = analysis['goroutine_patterns']
    report += f"## Goroutine Patterns ({len(patterns)} found)\n\n"

    for pattern in patterns:
        icon = "🔄" if pattern['type'] == "function_call" else "📝"
        report += f"- {icon} Line {pattern['line']}: `{pattern['call']}` ({pattern['type']})\n"

    # Issues
    if analysis['potential_issues']:
        report += "\n## Potential Issues\n\n"
        for issue in analysis['potential_issues']:
            severity_icon = {'error': '❌', 'warning': '⚠️', 'info': '💡'}.get(issue['severity'], '💡')
            report += f"{severity_icon} **{issue['type']}** (Line {issue.get('line', '?')})\n"
            report += f"   {issue['message']}\n"
            if 'suggestion' in issue:
                report += f"   💡 {issue['suggestion']}\n"
            report += "\n"

    # Recommendations
    if analysis['recommendations']:
        report += "## Recommendations\n\n"
        for rec in analysis['recommendations']:
            report += f"- 💡 {rec}\n"

    return report


def _format_channel_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the channel analysis report."""
    report = "# Channel Analysis Report\n\n"
    report += f"**File:** `{analysis['file_path']}`\n"
    report += f"**Pattern Type:** {analysis['pattern_type']}\n\n"

    # Channel declarations
    channels = analysis['channel_declarations']
    if channels:
        report += f"## Channel Declarations ({len(channels)} found)\n\n"
        for ch in channels:
            buffer_info = f"buffered({ch['buffer_size']})" if ch['is_buffered'] else "unbuffered"
            report += f"- Line {ch['line']}: `chan {ch['type']}` - {buffer_info}\n"

    # Channel operations
    operations = analysis['channel_operations']
    if operations:
        report += f"\n## Channel Operations ({len(operations)} found)\n\n"
        sends = [op for op in operations if op['type'] == 'send']
        receives = [op for op in operations if op['type'] == 'receive']

        report += f"**Sends:** {len(sends)}\n"
        for send in sends:
            report += f"- Line {send['line']}: `{send['channel']} <- {send['value']}`\n"

        report += f"\n**Receives:** {len(receives)}\n"
        for recv in receives:
            var_info = f" -> {recv['variable']}" if recv['variable'] else ""
            report += f"- Line {recv['line']}: `<-{recv['channel']}`{var_info}\n"

    # Select statements
    selects = analysis['select_statements']
    if selects:
        report += f"\n## Select Statements ({len(selects)} found)\n\n"
        for sel in selects:
            default_info = " (with default)" if sel['has_default'] else ""
            report += f"- Line {sel['line']}: {sel['case_count']} cases{default_info}\n"

    # Issues
    if analysis['issues']:
        report += "\n## Issues Found\n\n"
        for issue in analysis['issues']:
            severity_icon = {'error': '❌', 'warning': '⚠️', 'info': '💡'}.get(issue['severity'], '💡')
            report += f"{severity_icon} **{issue['type']}**\n"
            report += f"   {issue['message']}\n"
            if 'suggestion' in issue:
                report += f"   💡 {issue['suggestion']}\n"
            report += "\n"

    return report


def _format_race_detection_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the race condition detection report."""
    report = "# Race Condition Detection Report\n\n"
    report += f"**Directory:** `{analysis['directory']}`\n"
    report += f"**Files Analyzed:** {analysis['files_analyzed']}\n\n"

    # Potential races
    races = analysis['potential_races']
    if races:
        report += f"## Potential Race Conditions ({len(races)} found)\n\n"
        for race in races:
            severity_icon = {'error': '❌', 'warning': '⚠️', 'info': '💡'}.get(race['severity'], '💡')
            report += f"{severity_icon} **{race['type']}** in `{race['file']}`\n"
            report += f"   Line {race['line']}: {race['message']}\n\n"

    # Shared variables
    shared_vars = analysis['shared_variables']
    if shared_vars:
        report += f"## Shared Variables ({len(shared_vars)} found)\n\n"
        for var in shared_vars:
            report += f"- `{var['variable']}` in `{var['file']}` (declared line {var['declaration_line']})\n"
            report += f"  Accessed in {len(var['goroutine_accesses'])} goroutine(s)\n"

    # Unsafe patterns
    unsafe_patterns = analysis['unsafe_patterns']
    if unsafe_patterns:
        report += f"\n## Unsafe Patterns ({len(unsafe_patterns)} found)\n\n"
        for pattern in unsafe_patterns:
            severity_icon = {'error': '❌', 'warning': '⚠️', 'info': '💡'}.get(pattern['severity'], '💡')
            report += f"{severity_icon} **{pattern['type']}** in `{pattern['file']}`\n"
            report += f"   {pattern['message']}\n"
            report += f"   💡 {pattern['suggestion']}\n\n"

    # Race detector output
    if 'race_detector_output' in analysis:
        report += "## Go Race Detector\n\n"
        report += f"```\n{analysis['race_detector_output']}\n```\n"

    return report