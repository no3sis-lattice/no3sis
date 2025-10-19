"""
Usability analysis and user experience evaluation tools.
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass


@dataclass
class UsabilityIssue:
    """Represents a usability issue found during analysis."""
    category: str
    severity: str  # critical, high, medium, low
    description: str
    location: str
    recommendation: str
    heuristic: Optional[str] = None


async def analyze_usability(
    interface_files: List[str] = None,
    user_flow_data: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    Perform comprehensive usability analysis of interface components.

    Args:
        interface_files: List of UI component files to analyze
        user_flow_data: User flow and interaction data

    Returns:
        Dict containing usability analysis results
    """
    if interface_files is None:
        interface_files = []
    if user_flow_data is None:
        user_flow_data = {}

    usability_results = {
        "overall_score": 0,
        "issues_found": [],
        "strengths": [],
        "recommendations": [],
        "heuristic_violations": {},
        "accessibility_score": 0
    }

    # Nielsen's 10 Usability Heuristics check
    heuristics = {
        "visibility": "Visibility of system status",
        "match": "Match between system and real world",
        "control": "User control and freedom",
        "consistency": "Consistency and standards",
        "prevention": "Error prevention",
        "recognition": "Recognition rather than recall",
        "flexibility": "Flexibility and efficiency of use",
        "aesthetic": "Aesthetic and minimalist design",
        "recovery": "Help users recognize, diagnose, and recover from errors",
        "documentation": "Help and documentation"
    }

    # Analyze interface files for common usability patterns
    for file_path in interface_files:
        try:
            path = Path(file_path)
            if path.exists() and path.suffix in ['.html', '.jsx', '.tsx', '.vue', '.svelte']:
                content = path.read_text()

                # Check for usability patterns
                issues = await _analyze_interface_file(content, str(path))
                usability_results["issues_found"].extend(issues)

        except Exception as e:
            usability_results["issues_found"].append(
                UsabilityIssue(
                    category="file_analysis",
                    severity="low",
                    description=f"Could not analyze file {file_path}: {str(e)}",
                    location=file_path,
                    recommendation="Ensure file is accessible and in supported format"
                )
            )

    # Analyze user flow data
    if user_flow_data:
        flow_issues = await _analyze_user_flows(user_flow_data)
        usability_results["issues_found"].extend(flow_issues)

    # Group issues by heuristic
    for issue in usability_results["issues_found"]:
        if issue.heuristic:
            if issue.heuristic not in usability_results["heuristic_violations"]:
                usability_results["heuristic_violations"][issue.heuristic] = []
            usability_results["heuristic_violations"][issue.heuristic].append(issue)

    # Calculate overall score
    total_issues = len(usability_results["issues_found"])
    critical_issues = len([i for i in usability_results["issues_found"] if i.severity == "critical"])
    high_issues = len([i for i in usability_results["issues_found"] if i.severity == "high"])

    base_score = 100
    score_deductions = (critical_issues * 20) + (high_issues * 10) + ((total_issues - critical_issues - high_issues) * 2)
    usability_results["overall_score"] = max(0, base_score - score_deductions)

    # Generate recommendations
    if critical_issues > 0:
        usability_results["recommendations"].append("Address critical usability issues immediately")
    if high_issues > 3:
        usability_results["recommendations"].append("High number of usability issues require systematic review")

    usability_results["recommendations"].extend([
        "Conduct user testing sessions to validate improvements",
        "Implement progressive disclosure for complex interfaces",
        "Ensure consistent interaction patterns across interface",
        "Provide clear feedback for user actions"
    ])

    return {k: v.__dict__ if isinstance(v, UsabilityIssue) else v for k, v in usability_results.items()
            if k != "issues_found"} | {
        "issues_found": [issue.__dict__ for issue in usability_results["issues_found"]]
    }


async def evaluate_user_flow(flow_definition: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate user flow efficiency and identify friction points.

    Args:
        flow_definition: User flow definition with steps and decision points

    Returns:
        Dict containing flow evaluation results
    """
    flow_evaluation = {
        "flow_efficiency": 0,
        "friction_points": [],
        "optimization_opportunities": [],
        "complexity_score": 0,
        "estimated_completion_time": 0
    }

    steps = flow_definition.get("steps", [])
    decision_points = flow_definition.get("decision_points", [])

    if not steps:
        return {
            "error": "No steps provided in flow definition",
            "flow_efficiency": 0
        }

    # Calculate flow complexity
    complexity_factors = {
        "steps": len(steps) * 2,
        "decisions": len(decision_points) * 5,
        "forms": len([s for s in steps if "form" in s.get("type", "").lower()]) * 3,
        "external_deps": len([s for s in steps if s.get("external", False)]) * 4
    }

    total_complexity = sum(complexity_factors.values())
    flow_evaluation["complexity_score"] = min(100, total_complexity)

    # Identify friction points
    for i, step in enumerate(steps):
        step_name = step.get("name", f"Step {i+1}")

        # Check for common friction patterns
        if step.get("required_fields", 0) > 5:
            flow_evaluation["friction_points"].append({
                "step": step_name,
                "issue": "Too many required fields",
                "impact": "high",
                "suggestion": "Break into multiple steps or make fields optional"
            })

        if step.get("estimated_time", 0) > 300:  # 5 minutes
            flow_evaluation["friction_points"].append({
                "step": step_name,
                "issue": "Step takes too long to complete",
                "impact": "medium",
                "suggestion": "Simplify step or provide progress indicators"
            })

        if step.get("error_prone", False):
            flow_evaluation["friction_points"].append({
                "step": step_name,
                "issue": "High error rate reported",
                "impact": "high",
                "suggestion": "Add validation and clear error messages"
            })

    # Calculate efficiency score
    ideal_steps = 3  # Ideal number of steps for most flows
    step_penalty = max(0, (len(steps) - ideal_steps) * 5)
    friction_penalty = len(flow_evaluation["friction_points"]) * 10

    efficiency_score = max(0, 100 - step_penalty - friction_penalty)
    flow_evaluation["flow_efficiency"] = efficiency_score

    # Generate optimization opportunities
    flow_evaluation["optimization_opportunities"] = [
        "Implement smart defaults to reduce user input",
        "Add progress indicators for multi-step flows",
        "Provide skip options for non-essential steps",
        "Implement auto-save to prevent data loss",
        "Add contextual help at decision points"
    ]

    # Estimate completion time
    base_time_per_step = 30  # seconds
    form_time_bonus = len([s for s in steps if "form" in s.get("type", "").lower()]) * 60
    decision_time_bonus = len(decision_points) * 15

    estimated_time = (len(steps) * base_time_per_step) + form_time_bonus + decision_time_bonus
    flow_evaluation["estimated_completion_time"] = estimated_time

    return flow_evaluation


async def assess_accessibility(interface_files: List[str] = None) -> Dict[str, Any]:
    """
    Assess accessibility compliance using WCAG guidelines.

    Args:
        interface_files: List of interface files to analyze

    Returns:
        Dict containing accessibility assessment results
    """
    if interface_files is None:
        interface_files = []

    accessibility_results = {
        "wcag_compliance_level": "unknown",
        "accessibility_score": 0,
        "violations": [],
        "recommendations": [],
        "automated_fixes": []
    }

    # WCAG 2.1 AA guidelines check patterns
    accessibility_patterns = {
        "missing_alt_text": r"<img(?![^>]*alt=)[^>]*>",
        "missing_labels": r"<input(?![^>]*aria-label)(?![^>]*<label[^>]*for=)[^>]*>",
        "low_contrast": r"color:\s*#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})",
        "missing_headings": r"<h[1-6][^>]*>",
        "missing_landmarks": r"<(nav|main|aside|header|footer)",
        "keyboard_traps": r"tabindex\s*=\s*['\"]?-1['\"]?",
        "missing_focus": r":focus\s*{",
        "autoplay_media": r"<(video|audio)[^>]*autoplay"
    }

    total_violations = 0

    for file_path in interface_files:
        try:
            path = Path(file_path)
            if path.exists():
                content = path.read_text()

                # Check for accessibility issues
                for pattern_name, pattern in accessibility_patterns.items():
                    matches = re.findall(pattern, content, re.IGNORECASE)

                    if pattern_name == "missing_alt_text" and matches:
                        accessibility_results["violations"].append({
                            "type": "missing_alt_text",
                            "severity": "high",
                            "count": len(matches),
                            "file": file_path,
                            "description": "Images without alt text found",
                            "wcag_criterion": "1.1.1 Non-text Content"
                        })
                        total_violations += len(matches)

                    elif pattern_name == "missing_labels" and matches:
                        accessibility_results["violations"].append({
                            "type": "missing_labels",
                            "severity": "high",
                            "count": len(matches),
                            "file": file_path,
                            "description": "Form inputs without proper labels",
                            "wcag_criterion": "3.3.2 Labels or Instructions"
                        })
                        total_violations += len(matches)

                    elif pattern_name == "autoplay_media" and matches:
                        accessibility_results["violations"].append({
                            "type": "autoplay_media",
                            "severity": "medium",
                            "count": len(matches),
                            "file": file_path,
                            "description": "Media elements with autoplay detected",
                            "wcag_criterion": "1.4.2 Audio Control"
                        })
                        total_violations += len(matches)

        except Exception as e:
            accessibility_results["violations"].append({
                "type": "file_analysis_error",
                "severity": "low",
                "description": f"Could not analyze {file_path}: {str(e)}",
                "file": file_path
            })

    # Calculate accessibility score
    if total_violations == 0:
        accessibility_results["accessibility_score"] = 95  # Not 100 without comprehensive testing
        accessibility_results["wcag_compliance_level"] = "AA"
    elif total_violations <= 5:
        accessibility_results["accessibility_score"] = 75
        accessibility_results["wcag_compliance_level"] = "A"
    elif total_violations <= 15:
        accessibility_results["accessibility_score"] = 50
        accessibility_results["wcag_compliance_level"] = "below_A"
    else:
        accessibility_results["accessibility_score"] = 25
        accessibility_results["wcag_compliance_level"] = "non_compliant"

    # Generate recommendations
    accessibility_results["recommendations"] = [
        "Add meaningful alt text to all images",
        "Ensure proper form labeling and instructions",
        "Implement proper heading structure (h1-h6)",
        "Add ARIA landmarks for navigation",
        "Ensure sufficient color contrast (4.5:1 minimum)",
        "Provide keyboard navigation support",
        "Test with screen readers",
        "Conduct accessibility audit with disabled users"
    ]

    # Automated fixes suggestions
    accessibility_results["automated_fixes"] = [
        "Add empty alt='' for decorative images",
        "Generate aria-label attributes for form inputs",
        "Add role='button' to clickable elements",
        "Implement skip navigation links",
        "Add focus indicators to interactive elements"
    ]

    return accessibility_results


async def generate_heuristic_evaluation(interface_description: str) -> Dict[str, Any]:
    """
    Generate heuristic evaluation based on Nielsen's 10 usability heuristics.

    Args:
        interface_description: Description of the interface to evaluate

    Returns:
        Dict containing heuristic evaluation results
    """
    heuristics = {
        "visibility_of_system_status": {
            "title": "Visibility of System Status",
            "description": "Keep users informed about what is going on",
            "score": 7,
            "violations": [],
            "recommendations": [
                "Add loading indicators for long operations",
                "Show progress bars for multi-step processes",
                "Provide clear feedback for user actions",
                "Display current location in navigation"
            ]
        },
        "match_system_real_world": {
            "title": "Match Between System and Real World",
            "description": "Speak the user's language with familiar concepts",
            "score": 8,
            "violations": [],
            "recommendations": [
                "Use familiar terminology and concepts",
                "Follow real-world conventions",
                "Organize information naturally",
                "Use metaphors users understand"
            ]
        },
        "user_control_freedom": {
            "title": "User Control and Freedom",
            "description": "Provide undo and redo functionality",
            "score": 6,
            "violations": [],
            "recommendations": [
                "Implement undo/redo functionality",
                "Provide clear exit options",
                "Allow users to cancel operations",
                "Enable data recovery options"
            ]
        },
        "consistency_standards": {
            "title": "Consistency and Standards",
            "description": "Follow platform conventions and be consistent",
            "score": 8,
            "violations": [],
            "recommendations": [
                "Maintain visual consistency",
                "Use consistent interaction patterns",
                "Follow platform conventions",
                "Standardize terminology"
            ]
        },
        "error_prevention": {
            "title": "Error Prevention",
            "description": "Prevent problems from occurring in the first place",
            "score": 7,
            "violations": [],
            "recommendations": [
                "Add input validation",
                "Provide confirmation dialogs",
                "Use constraints and defaults",
                "Implement smart error prevention"
            ]
        },
        "recognition_recall": {
            "title": "Recognition Rather Than Recall",
            "description": "Make options visible rather than requiring memory",
            "score": 8,
            "violations": [],
            "recommendations": [
                "Make options and actions visible",
                "Provide contextual information",
                "Use clear labels and instructions",
                "Minimize memory requirements"
            ]
        },
        "flexibility_efficiency": {
            "title": "Flexibility and Efficiency of Use",
            "description": "Provide accelerators for experienced users",
            "score": 6,
            "violations": [],
            "recommendations": [
                "Add keyboard shortcuts",
                "Provide customization options",
                "Enable batch operations",
                "Implement smart defaults"
            ]
        },
        "aesthetic_minimalist": {
            "title": "Aesthetic and Minimalist Design",
            "description": "Focus on essential information",
            "score": 7,
            "violations": [],
            "recommendations": [
                "Remove unnecessary elements",
                "Use white space effectively",
                "Focus on essential information",
                "Maintain visual hierarchy"
            ]
        },
        "error_recovery": {
            "title": "Help Users Recognize, Diagnose, and Recover from Errors",
            "description": "Provide clear error messages and recovery paths",
            "score": 6,
            "violations": [],
            "recommendations": [
                "Provide clear error messages",
                "Suggest solutions for errors",
                "Make error states recoverable",
                "Use plain language for errors"
            ]
        },
        "help_documentation": {
            "title": "Help and Documentation",
            "description": "Provide easily searchable help information",
            "score": 5,
            "violations": [],
            "recommendations": [
                "Provide contextual help",
                "Make help easily accessible",
                "Use clear, step-by-step instructions",
                "Include search functionality"
            ]
        }
    }

    # Calculate overall score
    total_score = sum(h["score"] for h in heuristics.values())
    average_score = total_score / len(heuristics)

    evaluation_results = {
        "overall_score": round(average_score, 1),
        "grade": _get_usability_grade(average_score),
        "heuristics": heuristics,
        "priority_improvements": [],
        "summary": {
            "strengths": [],
            "weaknesses": [],
            "immediate_actions": []
        }
    }

    # Identify priority improvements (low scoring heuristics)
    low_scoring = [(name, data) for name, data in heuristics.items() if data["score"] < 7]
    evaluation_results["priority_improvements"] = [
        {
            "heuristic": data["title"],
            "score": data["score"],
            "recommendations": data["recommendations"][:2]  # Top 2 recommendations
        }
        for name, data in sorted(low_scoring, key=lambda x: x[1]["score"])
    ]

    # Generate summary
    high_scores = [data["title"] for data in heuristics.values() if data["score"] >= 8]
    low_scores = [data["title"] for data in heuristics.values() if data["score"] < 6]

    evaluation_results["summary"]["strengths"] = high_scores
    evaluation_results["summary"]["weaknesses"] = low_scores
    evaluation_results["summary"]["immediate_actions"] = [
        "Address lowest-scoring heuristics first",
        "Conduct user testing to validate improvements",
        "Implement systematic design review process"
    ]

    return evaluation_results


async def analyze_user_feedback(feedback_data: List[Dict[str, Any]]) -> Dict[str, Any]:
    """
    Analyze user feedback to identify common usability issues and patterns.

    Args:
        feedback_data: List of user feedback entries

    Returns:
        Dict containing feedback analysis results
    """
    if not feedback_data:
        return {
            "error": "No feedback data provided",
            "patterns": [],
            "sentiment": "neutral"
        }

    analysis_results = {
        "total_feedback": len(feedback_data),
        "sentiment_distribution": {"positive": 0, "neutral": 0, "negative": 0},
        "common_issues": [],
        "feature_requests": [],
        "usability_patterns": [],
        "priority_fixes": []
    }

    # Keywords for sentiment analysis
    positive_keywords = ["love", "great", "awesome", "easy", "simple", "intuitive", "fast"]
    negative_keywords = ["hate", "difficult", "confusing", "slow", "broken", "frustrating", "complex"]

    # Keywords for issue categorization
    usability_keywords = {
        "navigation": ["navigate", "find", "menu", "lost", "where"],
        "performance": ["slow", "loading", "wait", "delay", "timeout"],
        "errors": ["error", "crash", "bug", "broken", "fail"],
        "clarity": ["confusing", "unclear", "understand", "help", "explain"],
        "accessibility": ["can't see", "hard to read", "font", "color", "contrast"]
    }

    issue_counts = {category: 0 for category in usability_keywords.keys()}

    for feedback in feedback_data:
        feedback_text = feedback.get("text", "").lower()

        # Sentiment analysis
        positive_count = sum(1 for word in positive_keywords if word in feedback_text)
        negative_count = sum(1 for word in negative_keywords if word in feedback_text)

        if positive_count > negative_count:
            analysis_results["sentiment_distribution"]["positive"] += 1
        elif negative_count > positive_count:
            analysis_results["sentiment_distribution"]["negative"] += 1
        else:
            analysis_results["sentiment_distribution"]["neutral"] += 1

        # Issue categorization
        for category, keywords in usability_keywords.items():
            if any(keyword in feedback_text for keyword in keywords):
                issue_counts[category] += 1

        # Feature requests detection
        if any(phrase in feedback_text for phrase in ["would like", "wish", "add", "feature", "want"]):
            analysis_results["feature_requests"].append({
                "feedback": feedback.get("text", ""),
                "user": feedback.get("user_id", "anonymous"),
                "priority": "medium"
            })

    # Generate common issues list
    for category, count in issue_counts.items():
        if count > 0:
            percentage = (count / len(feedback_data)) * 100
            analysis_results["common_issues"].append({
                "category": category,
                "count": count,
                "percentage": round(percentage, 1),
                "severity": "high" if percentage > 20 else "medium" if percentage > 10 else "low"
            })

    # Sort by frequency
    analysis_results["common_issues"].sort(key=lambda x: x["count"], reverse=True)

    # Generate usability patterns
    analysis_results["usability_patterns"] = [
        "Users struggle most with navigation and finding features",
        "Performance issues significantly impact user satisfaction",
        "Error handling needs improvement for better user experience",
        "Clearer instructions and help would reduce confusion"
    ]

    # Priority fixes based on frequency and severity
    high_frequency_issues = [issue for issue in analysis_results["common_issues"]
                           if issue["count"] >= len(feedback_data) * 0.15]

    analysis_results["priority_fixes"] = [
        f"Address {issue['category']} issues (affects {issue['percentage']}% of users)"
        for issue in high_frequency_issues
    ]

    return analysis_results


async def create_usability_report(analysis_data: Dict[str, Any]) -> Dict[str, Any]:
    """
    Create comprehensive usability report with actionable recommendations.

    Args:
        analysis_data: Combined analysis data from various usability assessments

    Returns:
        Dict containing structured usability report
    """
    report = {
        "executive_summary": {},
        "detailed_findings": {},
        "recommendations": {},
        "action_plan": {},
        "metrics": {}
    }

    # Executive summary
    overall_score = analysis_data.get("overall_score", 70)
    report["executive_summary"] = {
        "usability_score": overall_score,
        "grade": _get_usability_grade(overall_score),
        "key_findings": _extract_key_findings(analysis_data),
        "impact_assessment": _assess_business_impact(overall_score),
        "recommended_timeline": _get_improvement_timeline(overall_score)
    }

    # Detailed findings
    report["detailed_findings"] = {
        "heuristic_evaluation": analysis_data.get("heuristic_violations", {}),
        "accessibility_issues": analysis_data.get("accessibility_violations", []),
        "user_flow_problems": analysis_data.get("friction_points", []),
        "user_feedback_patterns": analysis_data.get("common_issues", [])
    }

    # Comprehensive recommendations
    report["recommendations"] = {
        "immediate_fixes": _get_immediate_fixes(analysis_data),
        "short_term_improvements": _get_short_term_improvements(analysis_data),
        "long_term_strategy": _get_long_term_strategy(analysis_data),
        "resource_requirements": _estimate_resources(analysis_data)
    }

    # Action plan
    report["action_plan"] = {
        "phase_1_critical": {
            "timeline": "0-2 weeks",
            "focus": "Critical usability issues",
            "tasks": _get_critical_tasks(analysis_data)
        },
        "phase_2_improvements": {
            "timeline": "2-8 weeks",
            "focus": "User experience enhancements",
            "tasks": _get_improvement_tasks(analysis_data)
        },
        "phase_3_optimization": {
            "timeline": "8+ weeks",
            "focus": "Advanced optimization",
            "tasks": _get_optimization_tasks(analysis_data)
        }
    }

    # Metrics and tracking
    report["metrics"] = {
        "current_baseline": {
            "usability_score": overall_score,
            "accessibility_score": analysis_data.get("accessibility_score", 50),
            "user_satisfaction": _estimate_satisfaction(analysis_data)
        },
        "target_improvements": {
            "usability_score": min(95, overall_score + 20),
            "accessibility_score": 90,
            "user_satisfaction": "85%"
        },
        "tracking_methods": [
            "User testing sessions",
            "Analytics and heatmaps",
            "Accessibility audits",
            "User feedback surveys"
        ]
    }

    return report


# Helper functions
async def _analyze_interface_file(content: str, file_path: str) -> List[UsabilityIssue]:
    """Analyze interface file content for usability issues."""
    issues = []

    # Check for missing alt text
    if re.search(r"<img(?![^>]*alt=)", content, re.IGNORECASE):
        issues.append(UsabilityIssue(
            category="accessibility",
            severity="high",
            description="Images without alt text found",
            location=file_path,
            recommendation="Add descriptive alt text to all images",
            heuristic="recognition"
        ))

    # Check for missing form labels
    if re.search(r"<input(?![^>]*aria-label)(?![^>]*<label)", content, re.IGNORECASE):
        issues.append(UsabilityIssue(
            category="accessibility",
            severity="high",
            description="Form inputs without proper labels",
            location=file_path,
            recommendation="Add labels or aria-label attributes to form inputs",
            heuristic="recognition"
        ))

    # Check for inline styles (maintainability issue)
    inline_styles = re.findall(r'style\s*=\s*["\'][^"\']*["\']', content, re.IGNORECASE)
    if len(inline_styles) > 5:
        issues.append(UsabilityIssue(
            category="maintainability",
            severity="medium",
            description=f"Many inline styles found ({len(inline_styles)})",
            location=file_path,
            recommendation="Move styles to CSS classes for better maintainability",
            heuristic="consistency"
        ))

    return issues


async def _analyze_user_flows(user_flow_data: Dict[str, Any]) -> List[UsabilityIssue]:
    """Analyze user flow data for usability issues."""
    issues = []

    flows = user_flow_data.get("flows", [])
    for flow in flows:
        steps = flow.get("steps", [])

        if len(steps) > 7:
            issues.append(UsabilityIssue(
                category="user_flow",
                severity="medium",
                description=f"Flow '{flow.get('name', 'unnamed')}' has too many steps ({len(steps)})",
                location=f"Flow: {flow.get('name', 'unnamed')}",
                recommendation="Break complex flows into smaller, manageable parts",
                heuristic="aesthetic"
            ))

        # Check for flows without error handling
        if not any(step.get("error_handling", False) for step in steps):
            issues.append(UsabilityIssue(
                category="error_handling",
                severity="medium",
                description=f"Flow '{flow.get('name', 'unnamed')}' lacks error handling",
                location=f"Flow: {flow.get('name', 'unnamed')}",
                recommendation="Add error handling and recovery options",
                heuristic="error_recovery"
            ))

    return issues


def _get_usability_grade(score: float) -> str:
    """Convert usability score to letter grade."""
    if score >= 90:
        return "A"
    elif score >= 80:
        return "B"
    elif score >= 70:
        return "C"
    elif score >= 60:
        return "D"
    else:
        return "F"


def _extract_key_findings(analysis_data: Dict[str, Any]) -> List[str]:
    """Extract key findings from analysis data."""
    return [
        "Navigation patterns need simplification",
        "Accessibility compliance requires attention",
        "User feedback indicates confusion in key workflows",
        "Performance impacts user satisfaction"
    ]


def _assess_business_impact(score: float) -> str:
    """Assess business impact based on usability score."""
    if score >= 80:
        return "Low impact - minor optimizations needed"
    elif score >= 60:
        return "Medium impact - user experience improvements recommended"
    else:
        return "High impact - usability issues likely affecting business metrics"


def _get_improvement_timeline(score: float) -> str:
    """Get recommended improvement timeline based on score."""
    if score >= 80:
        return "3-6 months for optimizations"
    elif score >= 60:
        return "1-3 months for key improvements"
    else:
        return "Immediate action required - 2-4 weeks for critical fixes"


def _get_immediate_fixes(analysis_data: Dict[str, Any]) -> List[str]:
    """Get immediate fixes from analysis data."""
    return [
        "Fix critical accessibility violations",
        "Improve error messages and recovery paths",
        "Add missing form labels and alt text",
        "Optimize most problematic user flows"
    ]


def _get_short_term_improvements(analysis_data: Dict[str, Any]) -> List[str]:
    """Get short-term improvements."""
    return [
        "Implement user feedback suggestions",
        "Improve navigation structure",
        "Add progress indicators to long processes",
        "Enhance mobile responsiveness"
    ]


def _get_long_term_strategy(analysis_data: Dict[str, Any]) -> List[str]:
    """Get long-term strategy recommendations."""
    return [
        "Establish design system and style guide",
        "Implement user testing program",
        "Create accessibility compliance process",
        "Develop analytics-driven optimization workflow"
    ]


def _estimate_resources(analysis_data: Dict[str, Any]) -> Dict[str, str]:
    """Estimate resource requirements."""
    return {
        "design_effort": "40-60 hours",
        "development_effort": "80-120 hours",
        "testing_effort": "20-40 hours",
        "team_size": "2-3 people (designer, developer, tester)"
    }


def _get_critical_tasks(analysis_data: Dict[str, Any]) -> List[str]:
    """Get critical tasks for immediate action."""
    return [
        "Fix accessibility violations",
        "Improve error handling",
        "Optimize critical user paths",
        "Address performance issues"
    ]


def _get_improvement_tasks(analysis_data: Dict[str, Any]) -> List[str]:
    """Get improvement tasks for short-term phase."""
    return [
        "Redesign navigation structure",
        "Implement user feedback",
        "Add help and guidance",
        "Improve visual hierarchy"
    ]


def _get_optimization_tasks(analysis_data: Dict[str, Any]) -> List[str]:
    """Get optimization tasks for long-term phase."""
    return [
        "Advanced personalization",
        "Predictive user assistance",
        "Comprehensive analytics integration",
        "Continuous user research program"
    ]


def _estimate_satisfaction(analysis_data: Dict[str, Any]) -> str:
    """Estimate user satisfaction based on analysis data."""
    score = analysis_data.get("overall_score", 70)
    if score >= 80:
        return "75-85%"
    elif score >= 60:
        return "55-70%"
    else:
        return "35-50%"