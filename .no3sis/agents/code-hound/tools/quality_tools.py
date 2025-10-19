"""
Quality Assessment and Reporting Tools

Generate comprehensive quality reports with Code Hound's signature style.
Implements 4Q.Zero compressed reporting for maximum impact.
"""

from typing import Dict, List, Any
from datetime import datetime

async def calculate_quality_scores(analysis_results: Dict[str, Any]) -> Dict[str, int]:
    """
    Calculate comprehensive quality scores using Code Hound's standards.

    Returns scores 0-100 for:
    - Overall compliance
    - TDD score
    - KISS score
    - SOLID score
    - DRY score
    - No-shortcuts score
    """
    scores = {
        "overall": 0,
        "tdd": 0,
        "kiss": 0,
        "solid": 0,
        "dry": 0,
        "no_shortcuts": 0
    }

    # TDD Score
    tdd_analysis = analysis_results.get("tdd_analysis", {})
    scores["tdd"] = tdd_analysis.get("score", 0)

    # SOLID Score (average of all principles)
    solid_analysis = analysis_results.get("solid_analysis", {})
    solid_scores = solid_analysis.get("scores", {})
    if solid_scores:
        scores["solid"] = sum(solid_scores.values()) // len(solid_scores)

    # DRY Score
    dry_analysis = analysis_results.get("dry_analysis", {})
    scores["dry"] = dry_analysis.get("score", 0)

    # No-Shortcuts Score
    shortcuts_analysis = analysis_results.get("shortcuts_analysis", {})
    scores["no_shortcuts"] = shortcuts_analysis.get("score", 0)

    # KISS Score (based on complexity analysis)
    complexity_analysis = analysis_results.get("complexity", {})
    cyclomatic = complexity_analysis.get("cyclomatic_complexity", 0)
    nesting = complexity_analysis.get("nesting_depth", 0)

    # Calculate KISS score inversely proportional to complexity
    kiss_score = 100 - min(100, (cyclomatic * 3) + (nesting * 10))
    scores["kiss"] = max(0, kiss_score)

    # Overall score (weighted average)
    weights = {
        "tdd": 0.25,
        "solid": 0.2,
        "dry": 0.15,
        "kiss": 0.2,
        "no_shortcuts": 0.2
    }

    scores["overall"] = int(sum(scores[key] * weight for key, weight in weights.items()))

    return scores

async def generate_review_report(analysis_results: Dict[str, Any]) -> str:
    """
    Generate Code Hound's signature comprehensive review report.

    Uses 4Q.Zero compression for maximum semantic density and impact.
    """
    file_path = analysis_results.get("file_path", "unknown")
    language = analysis_results.get("language", "unknown")
    scores = analysis_results.get("quality_scores", {})

    # Header with Code Hound branding
    report = _generate_header(file_path, language)

    # Critical violations (show stoppers)
    critical_violations = _extract_critical_violations(analysis_results)
    if critical_violations:
        report += "\n🚨 **CRITICAL VIOLATIONS**\n"
        report += "```\n"
        for violation in critical_violations:
            report += f"❌ Line {violation['line']}: {violation['message']}\n"
        report += "```\n"

    # Major concerns
    major_violations = _extract_major_violations(analysis_results)
    if major_violations:
        report += "\n⚠️ **MAJOR CONCERNS**\n"
        report += "```\n"
        for violation in major_violations:
            report += f"⚠️  Line {violation['line']}: {violation['message']}\n"
        report += "```\n"

    # Detailed findings
    report += "\n🔍 **DETAILED FINDINGS**\n\n"

    # TDD Compliance
    tdd_analysis = analysis_results.get("tdd_analysis", {})
    report += f"#### TDD Compliance\n"
    report += f"- **Score**: {scores.get('tdd', 0)}/100\n"
    report += _format_tdd_findings(tdd_analysis)

    # KISS Violations
    report += f"\n#### KISS Violations\n"
    report += f"- **Score**: {scores.get('kiss', 0)}/100\n"
    report += _format_complexity_findings(analysis_results)

    # SOLID Breaches
    solid_analysis = analysis_results.get("solid_analysis", {})
    report += f"\n#### SOLID Breaches\n"
    report += f"- **Score**: {scores.get('solid', 0)}/100\n"
    report += _format_solid_findings(solid_analysis)

    # DRY Violations
    dry_analysis = analysis_results.get("dry_analysis", {})
    report += f"\n#### DRY Violations\n"
    report += f"- **Score**: {scores.get('dry', 0)}/100\n"
    report += _format_dry_findings(dry_analysis)

    # Shortcuts Detected
    shortcuts_analysis = analysis_results.get("shortcuts_analysis", {})
    report += f"\n#### Shortcuts Detected\n"
    report += f"- **Score**: {scores.get('no_shortcuts', 0)}/100\n"
    report += _format_shortcuts_findings(shortcuts_analysis)

    # Quality metrics
    report += "\n📊 **QUALITY METRICS**\n"
    report += f"- **Overall Compliance Score**: {scores.get('overall', 0)}/100\n"
    report += f"- **TDD Score**: {scores.get('tdd', 0)}/100\n"
    report += f"- **KISS Score**: {scores.get('kiss', 0)}/100\n"
    report += f"- **SOLID Score**: {scores.get('solid', 0)}/100\n"
    report += f"- **DRY Score**: {scores.get('dry', 0)}/100\n"
    report += f"- **No-Shortcuts Score**: {scores.get('no_shortcuts', 0)}/100\n"

    # Required actions
    report += "\n🎯 **REQUIRED ACTIONS**\n"
    actions = _generate_required_actions(analysis_results)
    for i, action in enumerate(actions, 1):
        report += f"{i}. {action}\n"

    # Recommendations
    report += "\n💡 **RECOMMENDATIONS**\n"
    recommendations = _generate_recommendations(analysis_results, scores)
    for rec in recommendations:
        report += f"- {rec}\n"

    # Final verdict
    report += "\n" + _generate_final_verdict(scores)

    return report

def _generate_header(file_path: str, language: str) -> str:
    """Generate Code Hound header."""
    return f"""
🐕 **CODE HOUND REVIEW REPORT**
═══════════════════════════════════

**File**: {file_path}
**Language**: {language}
**Timestamp**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}
**Reviewer**: Code Hound (Uncompromising Quality Enforcer)

*"This shortcut stops here. Fix it properly or don't ship it."*
"""

def _extract_critical_violations(results: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Extract all critical severity violations."""
    critical = []

    for analysis_type in ["tdd_analysis", "solid_analysis", "dry_analysis", "shortcuts_analysis"]:
        analysis = results.get(analysis_type, {})
        violations = analysis.get("violations", [])
        critical.extend([v for v in violations if v.get("severity") == "critical"])

    return sorted(critical, key=lambda x: x.get("line", 0))

def _extract_major_violations(results: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Extract all major severity violations."""
    major = []

    for analysis_type in ["tdd_analysis", "solid_analysis", "dry_analysis", "shortcuts_analysis"]:
        analysis = results.get(analysis_type, {})
        violations = analysis.get("violations", [])
        major.extend([v for v in violations if v.get("severity") == "major"])

    return sorted(major, key=lambda x: x.get("line", 0))

def _format_tdd_findings(tdd_analysis: Dict[str, Any]) -> str:
    """Format TDD analysis findings."""
    if not tdd_analysis:
        return "- No TDD analysis performed\n"

    evidence = tdd_analysis.get("evidence", {})
    findings = []

    if evidence.get("has_tests"):
        findings.append("✅ Tests detected")
    else:
        findings.append("❌ No tests found")

    if evidence.get("test_file_exists"):
        findings.append("✅ Test file exists")
    else:
        findings.append("❌ Missing test file")

    violations = tdd_analysis.get("violations", [])
    if violations:
        findings.append(f"⚠️  {len(violations)} TDD violations")

    return "- " + "\n- ".join(findings) + "\n"

def _format_complexity_findings(results: Dict[str, Any]) -> str:
    """Format complexity/KISS findings."""
    complexity = results.get("complexity", {})
    if not complexity:
        return "- No complexity analysis available\n"

    findings = []

    cyclomatic = complexity.get("cyclomatic_complexity", 0)
    if cyclomatic > 10:
        findings.append(f"⚠️  High cyclomatic complexity: {cyclomatic}")
    else:
        findings.append(f"✅ Acceptable complexity: {cyclomatic}")

    nesting = complexity.get("nesting_depth", 0)
    if nesting > 4:
        findings.append(f"⚠️  Deep nesting: {nesting} levels")
    else:
        findings.append(f"✅ Reasonable nesting: {nesting} levels")

    complexity_issues = results.get("complexity_issues", [])
    if complexity_issues:
        findings.append(f"⚠️  {len(complexity_issues)} complexity issues")

    return "- " + "\n- ".join(findings) + "\n"

def _format_solid_findings(solid_analysis: Dict[str, Any]) -> str:
    """Format SOLID principles findings."""
    if not solid_analysis:
        return "- No SOLID analysis performed\n"

    scores = solid_analysis.get("scores", {})
    findings = []

    principles = {
        "S": "Single Responsibility",
        "O": "Open/Closed",
        "L": "Liskov Substitution",
        "I": "Interface Segregation",
        "D": "Dependency Inversion"
    }

    for letter, name in principles.items():
        score = scores.get(letter, 0)
        if score >= 80:
            findings.append(f"✅ {name}: {score}/100")
        elif score >= 60:
            findings.append(f"⚠️  {name}: {score}/100")
        else:
            findings.append(f"❌ {name}: {score}/100")

    return "- " + "\n- ".join(findings) + "\n"

def _format_dry_findings(dry_analysis: Dict[str, Any]) -> str:
    """Format DRY principle findings."""
    if not dry_analysis:
        return "- No DRY analysis performed\n"

    violations = dry_analysis.get("violations", [])
    findings = []

    duplication_count = len([v for v in violations if v.get("type") == "code_duplication"])
    if duplication_count:
        findings.append(f"⚠️  {duplication_count} code duplication(s)")

    magic_count = len([v for v in violations if "magic" in v.get("type", "")])
    if magic_count:
        findings.append(f"⚠️  {magic_count} magic number(s)")

    if not violations:
        findings.append("✅ No DRY violations detected")

    return "- " + "\n- ".join(findings) + "\n"

def _format_shortcuts_findings(shortcuts_analysis: Dict[str, Any]) -> str:
    """Format shortcuts/technical debt findings."""
    if not shortcuts_analysis:
        return "- No shortcuts analysis performed\n"

    violations = shortcuts_analysis.get("violations", [])
    debt_level = shortcuts_analysis.get("debt_level", "unknown")

    findings = [f"📊 Technical debt level: {debt_level.upper()}"]

    if violations:
        by_type = {}
        for violation in violations:
            v_type = violation.get("type", "unknown")
            by_type[v_type] = by_type.get(v_type, 0) + 1

        for v_type, count in by_type.items():
            findings.append(f"⚠️  {v_type.replace('_', ' ').title()}: {count}")
    else:
        findings.append("✅ No shortcuts detected - Clean code!")

    return "- " + "\n- ".join(findings) + "\n"

def _generate_required_actions(results: Dict[str, Any]) -> List[str]:
    """Generate prioritized list of required actions."""
    actions = []

    # Critical violations first
    critical_violations = _extract_critical_violations(results)
    for violation in critical_violations[:3]:  # Top 3 critical
        actions.append(f"🚨 CRITICAL: Fix {violation['message']} (Line {violation['line']})")

    # Major violations
    major_violations = _extract_major_violations(results)
    for violation in major_violations[:2]:  # Top 2 major
        actions.append(f"⚠️  MAJOR: Address {violation['message']} (Line {violation['line']})")

    # TDD requirements
    tdd_analysis = results.get("tdd_analysis", {})
    if not tdd_analysis.get("evidence", {}).get("has_tests"):
        actions.append("📝 Implement comprehensive test coverage")

    # Complexity reduction
    complexity = results.get("complexity", {})
    if complexity.get("cyclomatic_complexity", 0) > 10:
        actions.append("🔧 Refactor to reduce cyclomatic complexity")

    if not actions:
        actions.append("✅ Code meets standards - continue with current practices")

    return actions

def _generate_recommendations(results: Dict[str, Any], scores: Dict[str, int]) -> List[str]:
    """Generate improvement recommendations."""
    recommendations = []

    # Based on scores, suggest improvements
    if scores.get("tdd", 0) < 80:
        recommendations.append("Implement test-first development practices")
        recommendations.append("Add missing test coverage for public methods")

    if scores.get("solid", 0) < 70:
        recommendations.append("Review class responsibilities and dependencies")
        recommendations.append("Consider applying SOLID principle refactoring")

    if scores.get("dry", 0) < 85:
        recommendations.append("Extract common patterns into reusable functions")
        recommendations.append("Create configuration for repeated values")

    if scores.get("kiss", 0) < 75:
        recommendations.append("Simplify complex functions and reduce nesting")
        recommendations.append("Break down large methods into smaller units")

    # Always add Code Hound philosophy
    if scores.get("overall", 0) >= 90:
        recommendations.append("🏆 Excellent work! This code meets Code Hound standards")
    else:
        recommendations.append("📚 Study clean code principles and refactoring patterns")

    return recommendations

def _generate_final_verdict(scores: Dict[str, int]) -> str:
    """Generate Code Hound's final verdict."""
    overall_score = scores.get("overall", 0)

    if overall_score >= 90:
        return """
═══════════════════════════════════

🟢 **APPROVED**

*"This code meets the standards. I'm proud to let it pass."*

- Code Hound
═══════════════════════════════════
"""

    elif overall_score >= 70:
        return """
═══════════════════════════════════

🟡 **CONDITIONAL**

*"Fix the critical issues, then we can talk."*

This code shows promise but has violations that must be addressed
before it can pass Code Hound's standards.

- Code Hound
═══════════════════════════════════
"""

    else:
        return """
═══════════════════════════════════

🔴 **REJECTED**

*"This needs significant rework. No shortcuts accepted."*

Multiple violations detected. This code requires substantial
improvement before it meets professional standards.

Remember: Complexity is the enemy. Simplify or justify.

- Code Hound
═══════════════════════════════════
"""

async def format_violations_report(violations: List[Dict[str, Any]]) -> str:
    """Format violations into a readable report."""
    if not violations:
        return "✅ No violations detected!"

    report = f"Found {len(violations)} violations:\n\n"

    # Group by severity
    by_severity = {"critical": [], "major": [], "medium": [], "low": []}
    for violation in violations:
        severity = violation.get("severity", "medium")
        by_severity[severity].append(violation)

    for severity in ["critical", "major", "medium", "low"]:
        if by_severity[severity]:
            report += f"\n**{severity.upper()} VIOLATIONS:**\n"
            for violation in by_severity[severity]:
                report += f"- Line {violation.get('line', '?')}: {violation.get('message', 'Unknown violation')}\n"

    return report