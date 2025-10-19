"""
Visual design analysis and improvement tools.
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass
import colorsys


@dataclass
class DesignIssue:
    """Represents a design issue found during analysis."""
    category: str
    severity: str  # critical, high, medium, low
    description: str
    location: str
    recommendation: str
    before_value: Optional[str] = None
    suggested_value: Optional[str] = None


async def analyze_visual_hierarchy(
    interface_files: List[str] = None,
    design_specs: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    Analyze visual hierarchy and information architecture.

    Args:
        interface_files: List of interface files to analyze
        design_specs: Design specifications and style guide

    Returns:
        Dict containing visual hierarchy analysis
    """
    if interface_files is None:
        interface_files = []
    if design_specs is None:
        design_specs = {}

    hierarchy_analysis = {
        "hierarchy_score": 0,
        "issues_found": [],
        "strengths": [],
        "recommendations": [],
        "heading_structure": {},
        "visual_weight_analysis": {}
    }

    heading_patterns = {
        "h1": r"<h1[^>]*>(.*?)</h1>",
        "h2": r"<h2[^>]*>(.*?)</h2>",
        "h3": r"<h3[^>]*>(.*?)</h3>",
        "h4": r"<h4[^>]*>(.*?)</h4>",
        "h5": r"<h5[^>]*>(.*?)</h5>",
        "h6": r"<h6[^>]*>(.*?)</h6>"
    }

    all_headings = {}
    font_sizes = []
    color_usage = []

    for file_path in interface_files:
        try:
            path = Path(file_path)
            if path.exists() and path.suffix in ['.html', '.jsx', '.tsx', '.vue', '.svelte']:
                content = path.read_text()

                # Analyze heading structure
                file_headings = {}
                for level, pattern in heading_patterns.items():
                    matches = re.findall(pattern, content, re.IGNORECASE | re.DOTALL)
                    if matches:
                        file_headings[level] = len(matches)
                        all_headings[level] = all_headings.get(level, 0) + len(matches)

                # Check for proper heading hierarchy
                heading_levels = list(file_headings.keys())
                if heading_levels:
                    if 'h1' not in heading_levels:
                        hierarchy_analysis["issues_found"].append(DesignIssue(
                            category="heading_structure",
                            severity="high",
                            description="No H1 heading found in page",
                            location=file_path,
                            recommendation="Add a main H1 heading to establish page hierarchy"
                        ))

                    # Check for skipped heading levels
                    heading_numbers = [int(h[1]) for h in heading_levels]
                    heading_numbers.sort()
                    for i in range(len(heading_numbers) - 1):
                        if heading_numbers[i + 1] - heading_numbers[i] > 1:
                            hierarchy_analysis["issues_found"].append(DesignIssue(
                                category="heading_structure",
                                severity="medium",
                                description=f"Skipped heading level from h{heading_numbers[i]} to h{heading_numbers[i + 1]}",
                                location=file_path,
                                recommendation="Use sequential heading levels for proper hierarchy"
                            ))

                # Analyze font sizes in CSS
                font_size_matches = re.findall(r"font-size:\s*([^;]+)", content, re.IGNORECASE)
                font_sizes.extend(font_size_matches)

                # Analyze color usage
                color_matches = re.findall(r"color:\s*([^;]+)", content, re.IGNORECASE)
                color_usage.extend(color_matches)

        except Exception as e:
            hierarchy_analysis["issues_found"].append(DesignIssue(
                category="analysis_error",
                severity="low",
                description=f"Could not analyze {file_path}: {str(e)}",
                location=file_path,
                recommendation="Ensure file is accessible and properly formatted"
            ))

    # Analyze font size consistency
    unique_font_sizes = list(set([size.strip() for size in font_sizes]))
    if len(unique_font_sizes) > 8:
        hierarchy_analysis["issues_found"].append(DesignIssue(
            category="typography",
            severity="medium",
            description=f"Too many font sizes used ({len(unique_font_sizes)})",
            location="Global",
            recommendation="Limit font sizes to 4-6 distinct values for better consistency"
        ))

    # Analyze color consistency
    unique_colors = list(set([color.strip() for color in color_usage]))
    if len(unique_colors) > 12:
        hierarchy_analysis["issues_found"].append(DesignIssue(
            category="color_scheme",
            severity="medium",
            description=f"Too many colors used ({len(unique_colors)})",
            location="Global",
            recommendation="Establish a consistent color palette with primary, secondary, and accent colors"
        ))

    # Store analysis data
    hierarchy_analysis["heading_structure"] = all_headings
    hierarchy_analysis["visual_weight_analysis"] = {
        "font_size_variety": len(unique_font_sizes),
        "color_variety": len(unique_colors),
        "consistency_score": _calculate_consistency_score(unique_font_sizes, unique_colors)
    }

    # Calculate overall hierarchy score
    issues_count = len(hierarchy_analysis["issues_found"])
    critical_issues = len([i for i in hierarchy_analysis["issues_found"] if i.severity == "critical"])
    high_issues = len([i for i in hierarchy_analysis["issues_found"] if i.severity == "high"])

    base_score = 100
    score_deduction = (critical_issues * 25) + (high_issues * 15) + ((issues_count - critical_issues - high_issues) * 5)
    hierarchy_analysis["hierarchy_score"] = max(0, base_score - score_deduction)

    # Generate recommendations
    hierarchy_analysis["recommendations"] = [
        "Establish consistent heading hierarchy (H1 → H2 → H3)",
        "Limit font sizes to 4-6 distinct values",
        "Use consistent color palette throughout interface",
        "Ensure proper visual weight progression",
        "Implement typography scale for consistency"
    ]

    return {k: v.__dict__ if isinstance(v, DesignIssue) else v for k, v in hierarchy_analysis.items()
            if k != "issues_found"} | {
        "issues_found": [issue.__dict__ for issue in hierarchy_analysis["issues_found"]]
    }


async def evaluate_color_scheme(
    color_palette: List[str] = None,
    interface_files: List[str] = None
) -> Dict[str, Any]:
    """
    Evaluate color scheme for accessibility, harmony, and brand consistency.

    Args:
        color_palette: List of colors in the design system
        interface_files: Interface files to analyze for color usage

    Returns:
        Dict containing color scheme evaluation
    """
    if color_palette is None:
        color_palette = []
    if interface_files is None:
        interface_files = []

    color_evaluation = {
        "accessibility_score": 0,
        "harmony_score": 0,
        "contrast_issues": [],
        "color_analysis": {},
        "recommendations": [],
        "palette_suggestions": []
    }

    # If no palette provided, extract from files
    if not color_palette and interface_files:
        extracted_colors = []
        for file_path in interface_files:
            try:
                path = Path(file_path)
                if path.exists():
                    content = path.read_text()
                    # Extract hex colors
                    hex_colors = re.findall(r"#[0-9a-fA-F]{3,6}", content)
                    # Extract rgb colors
                    rgb_colors = re.findall(r"rgb\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)", content)

                    extracted_colors.extend(hex_colors)
                    for r, g, b in rgb_colors:
                        extracted_colors.append(f"rgb({r}, {g}, {b})")
            except:
                continue

        color_palette = list(set(extracted_colors))

    if not color_palette:
        return {
            "error": "No colors found to analyze",
            "recommendations": ["Establish a consistent color palette"]
        }

    # Analyze each color
    color_data = []
    for color in color_palette[:20]:  # Limit to 20 colors for analysis
        color_info = await _analyze_color_properties(color)
        if color_info:
            color_data.append(color_info)

    color_evaluation["color_analysis"] = {
        "total_colors": len(color_palette),
        "analyzed_colors": len(color_data),
        "color_properties": color_data
    }

    # Check color harmony
    if len(color_data) >= 2:
        harmony_score = _calculate_color_harmony(color_data)
        color_evaluation["harmony_score"] = harmony_score
    else:
        color_evaluation["harmony_score"] = 50

    # Check accessibility (contrast ratios)
    contrast_issues = []
    for i, color1 in enumerate(color_data):
        for j, color2 in enumerate(color_data[i+1:], i+1):
            if color1 and color2:
                contrast_ratio = _calculate_contrast_ratio(color1, color2)

                if contrast_ratio < 4.5:  # WCAG AA minimum
                    contrast_issues.append({
                        "color1": color1.get("original", ""),
                        "color2": color2.get("original", ""),
                        "contrast_ratio": round(contrast_ratio, 2),
                        "severity": "high" if contrast_ratio < 3 else "medium",
                        "recommendation": "Increase contrast for better accessibility"
                    })

    color_evaluation["contrast_issues"] = contrast_issues

    # Calculate accessibility score
    if not contrast_issues:
        color_evaluation["accessibility_score"] = 95
    elif len(contrast_issues) <= 2:
        color_evaluation["accessibility_score"] = 75
    elif len(contrast_issues) <= 5:
        color_evaluation["accessibility_score"] = 50
    else:
        color_evaluation["accessibility_score"] = 25

    # Generate recommendations
    recommendations = []

    if len(color_palette) > 12:
        recommendations.append("Reduce color palette to 8-12 colors for better consistency")

    if contrast_issues:
        recommendations.append("Improve color contrast ratios for accessibility compliance")

    if color_evaluation["harmony_score"] < 60:
        recommendations.append("Consider using color harmony principles (complementary, triadic, etc.)")

    recommendations.extend([
        "Define primary, secondary, and accent color roles",
        "Ensure sufficient contrast between text and backgrounds",
        "Test colors with color blindness simulators",
        "Document color usage guidelines"
    ])

    color_evaluation["recommendations"] = recommendations

    # Generate palette suggestions
    if color_data:
        color_evaluation["palette_suggestions"] = _generate_palette_suggestions(color_data)

    return color_evaluation


async def assess_typography(
    interface_files: List[str] = None,
    typography_specs: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    Assess typography choices for readability, hierarchy, and consistency.

    Args:
        interface_files: Interface files to analyze
        typography_specs: Typography specifications

    Returns:
        Dict containing typography assessment
    """
    if interface_files is None:
        interface_files = []
    if typography_specs is None:
        typography_specs = {}

    typography_assessment = {
        "readability_score": 0,
        "consistency_score": 0,
        "font_analysis": {},
        "issues_found": [],
        "recommendations": []
    }

    fonts_found = set()
    font_sizes = []
    line_heights = []
    font_weights = []

    for file_path in interface_files:
        try:
            path = Path(file_path)
            if path.exists():
                content = path.read_text()

                # Extract typography properties
                font_family_matches = re.findall(r"font-family:\s*([^;]+)", content, re.IGNORECASE)
                fonts_found.update([f.strip().strip("'\"") for f in font_family_matches])

                font_size_matches = re.findall(r"font-size:\s*([^;]+)", content, re.IGNORECASE)
                font_sizes.extend([f.strip() for f in font_size_matches])

                line_height_matches = re.findall(r"line-height:\s*([^;]+)", content, re.IGNORECASE)
                line_heights.extend([l.strip() for l in line_height_matches])

                font_weight_matches = re.findall(r"font-weight:\s*([^;]+)", content, re.IGNORECASE)
                font_weights.extend([w.strip() for w in font_weight_matches])

        except Exception:
            continue

    # Analyze fonts
    unique_fonts = list(fonts_found)
    unique_font_sizes = list(set(font_sizes))
    unique_line_heights = list(set(line_heights))
    unique_font_weights = list(set(font_weights))

    typography_assessment["font_analysis"] = {
        "fonts_used": len(unique_fonts),
        "font_sizes": len(unique_font_sizes),
        "line_heights": len(unique_line_heights),
        "font_weights": len(unique_font_weights),
        "font_list": unique_fonts[:10],  # Show first 10
        "size_list": unique_font_sizes[:10]
    }

    # Check for too many fonts
    if len(unique_fonts) > 3:
        typography_assessment["issues_found"].append({
            "category": "font_consistency",
            "severity": "medium",
            "description": f"Too many font families used ({len(unique_fonts)})",
            "recommendation": "Limit to 2-3 font families maximum"
        })

    # Check for too many font sizes
    if len(unique_font_sizes) > 8:
        typography_assessment["issues_found"].append({
            "category": "size_consistency",
            "severity": "medium",
            "description": f"Too many font sizes used ({len(unique_font_sizes)})",
            "recommendation": "Establish a typographic scale with 4-6 sizes"
        })

    # Check for font size readability
    small_sizes = [size for size in unique_font_sizes if 'px' in size and int(re.findall(r'\d+', size)[0]) < 14]
    if small_sizes:
        typography_assessment["issues_found"].append({
            "category": "readability",
            "severity": "high",
            "description": f"Font sizes below 14px found: {small_sizes[:3]}",
            "recommendation": "Use minimum 14px for body text readability"
        })

    # Calculate scores
    consistency_penalty = 0
    if len(unique_fonts) > 3:
        consistency_penalty += 20
    if len(unique_font_sizes) > 8:
        consistency_penalty += 15

    typography_assessment["consistency_score"] = max(0, 100 - consistency_penalty)

    readability_penalty = len([i for i in typography_assessment["issues_found"]
                              if i["category"] == "readability"]) * 20
    typography_assessment["readability_score"] = max(0, 100 - readability_penalty)

    # Generate recommendations
    recommendations = [
        "Establish a typographic hierarchy with clear size relationships",
        "Use adequate line height (1.4-1.6) for body text",
        "Ensure sufficient contrast between text and background",
        "Limit font families to 2-3 maximum",
        "Use consistent font weights throughout interface"
    ]

    if small_sizes:
        recommendations.insert(0, "Increase small font sizes to minimum 14px")

    if len(unique_fonts) > 3:
        recommendations.insert(0, "Reduce number of font families for consistency")

    typography_assessment["recommendations"] = recommendations

    return typography_assessment


async def generate_design_suggestions(
    current_design: Dict[str, Any],
    target_goals: List[str] = None
) -> Dict[str, Any]:
    """
    Generate design improvement suggestions based on current state and goals.

    Args:
        current_design: Current design analysis data
        target_goals: List of design goals to achieve

    Returns:
        Dict containing design suggestions
    """
    if target_goals is None:
        target_goals = ["improve_usability", "enhance_accessibility", "increase_conversion"]

    suggestions = {
        "priority_improvements": [],
        "color_suggestions": [],
        "typography_suggestions": [],
        "layout_suggestions": [],
        "interaction_suggestions": [],
        "implementation_roadmap": {}
    }

    # Analyze current state
    usability_score = current_design.get("usability_score", 70)
    accessibility_score = current_design.get("accessibility_score", 60)
    visual_score = current_design.get("visual_hierarchy_score", 65)

    # Priority improvements based on scores
    if accessibility_score < 70:
        suggestions["priority_improvements"].append({
            "area": "Accessibility",
            "current_score": accessibility_score,
            "target_score": 90,
            "impact": "high",
            "effort": "medium",
            "actions": [
                "Improve color contrast ratios",
                "Add proper alt text to images",
                "Implement keyboard navigation",
                "Add ARIA labels where needed"
            ]
        })

    if usability_score < 75:
        suggestions["priority_improvements"].append({
            "area": "Usability",
            "current_score": usability_score,
            "target_score": 85,
            "impact": "high",
            "effort": "high",
            "actions": [
                "Simplify navigation structure",
                "Improve error handling and feedback",
                "Optimize user flows",
                "Add help and guidance features"
            ]
        })

    if visual_score < 70:
        suggestions["priority_improvements"].append({
            "area": "Visual Design",
            "current_score": visual_score,
            "target_score": 80,
            "impact": "medium",
            "effort": "medium",
            "actions": [
                "Establish consistent visual hierarchy",
                "Improve typography scale",
                "Refine color palette",
                "Enhance spacing and layout"
            ]
        })

    # Goal-specific suggestions
    if "improve_usability" in target_goals:
        suggestions["interaction_suggestions"] = [
            "Add hover states for interactive elements",
            "Implement progressive disclosure for complex features",
            "Provide clear feedback for user actions",
            "Optimize touch targets for mobile (44px minimum)"
        ]

    if "enhance_accessibility" in target_goals:
        suggestions["color_suggestions"] = [
            "Ensure 4.5:1 contrast ratio for normal text",
            "Use color plus text/icons to convey information",
            "Test with color blindness simulators",
            "Implement dark mode support"
        ]

    if "increase_conversion" in target_goals:
        suggestions["layout_suggestions"] = [
            "Simplify primary call-to-action placement",
            "Reduce visual clutter on key pages",
            "Improve page loading speed",
            "Add trust indicators and social proof"
        ]

    # Typography suggestions
    font_count = current_design.get("font_analysis", {}).get("fonts_used", 0)
    if font_count > 3:
        suggestions["typography_suggestions"].append(
            "Reduce font families to 2-3 maximum for consistency"
        )

    suggestions["typography_suggestions"].extend([
        "Establish clear typographic hierarchy",
        "Use appropriate font sizes for different screen sizes",
        "Ensure adequate line spacing (1.4-1.6)",
        "Choose fonts that support your brand personality"
    ])

    # Implementation roadmap
    suggestions["implementation_roadmap"] = {
        "phase_1_critical": {
            "timeline": "2-4 weeks",
            "focus": "Accessibility and critical usability fixes",
            "estimated_effort": "40-60 hours"
        },
        "phase_2_improvements": {
            "timeline": "4-8 weeks",
            "focus": "Visual design enhancements and user experience",
            "estimated_effort": "60-100 hours"
        },
        "phase_3_optimization": {
            "timeline": "8-12 weeks",
            "focus": "Advanced features and optimization",
            "estimated_effort": "40-80 hours"
        }
    }

    return suggestions


async def create_style_guide(design_analysis: Dict[str, Any]) -> Dict[str, Any]:
    """
    Create a comprehensive style guide based on design analysis.

    Args:
        design_analysis: Combined design analysis data

    Returns:
        Dict containing style guide specifications
    """
    style_guide = {
        "color_system": {},
        "typography_system": {},
        "spacing_system": {},
        "component_guidelines": {},
        "interaction_patterns": {},
        "accessibility_standards": {}
    }

    # Extract color system from analysis
    colors = design_analysis.get("color_analysis", {}).get("analyzed_colors", [])
    if colors:
        # Suggest primary/secondary/accent colors
        style_guide["color_system"] = {
            "primary": colors[0].get("original", "#007bff") if colors else "#007bff",
            "secondary": colors[1].get("original", "#6c757d") if len(colors) > 1 else "#6c757d",
            "accent": colors[2].get("original", "#28a745") if len(colors) > 2 else "#28a745",
            "neutral": {
                "white": "#ffffff",
                "light_gray": "#f8f9fa",
                "gray": "#6c757d",
                "dark_gray": "#343a40",
                "black": "#000000"
            },
            "semantic": {
                "success": "#28a745",
                "warning": "#ffc107",
                "danger": "#dc3545",
                "info": "#17a2b8"
            },
            "usage_guidelines": [
                "Use primary color for main actions and brand elements",
                "Use secondary color for less important actions",
                "Use accent color sparingly for highlights",
                "Ensure 4.5:1 contrast ratio for text"
            ]
        }

    # Typography system
    font_analysis = design_analysis.get("font_analysis", {})
    fonts = font_analysis.get("font_list", [])

    style_guide["typography_system"] = {
        "font_families": {
            "primary": fonts[0] if fonts else "Inter, -apple-system, BlinkMacSystemFont, sans-serif",
            "secondary": fonts[1] if len(fonts) > 1 else "Georgia, serif",
            "monospace": "Monaco, Menlo, monospace"
        },
        "font_scale": {
            "h1": {"size": "2.5rem", "weight": "700", "line_height": "1.2"},
            "h2": {"size": "2rem", "weight": "600", "line_height": "1.3"},
            "h3": {"size": "1.75rem", "weight": "600", "line_height": "1.3"},
            "h4": {"size": "1.5rem", "weight": "500", "line_height": "1.4"},
            "h5": {"size": "1.25rem", "weight": "500", "line_height": "1.4"},
            "h6": {"size": "1rem", "weight": "500", "line_height": "1.4"},
            "body": {"size": "1rem", "weight": "400", "line_height": "1.6"},
            "small": {"size": "0.875rem", "weight": "400", "line_height": "1.5"},
            "caption": {"size": "0.75rem", "weight": "400", "line_height": "1.4"}
        },
        "usage_guidelines": [
            "Use heading hierarchy consistently (h1 → h2 → h3)",
            "Maintain minimum 14px font size for body text",
            "Use appropriate line height for readability",
            "Limit font weights to 3-4 variations"
        ]
    }

    # Spacing system
    style_guide["spacing_system"] = {
        "base_unit": "8px",
        "scale": {
            "xs": "4px",
            "sm": "8px",
            "md": "16px",
            "lg": "24px",
            "xl": "32px",
            "2xl": "48px",
            "3xl": "64px"
        },
        "usage_guidelines": [
            "Use consistent spacing multiples of 8px",
            "Apply more spacing between unrelated elements",
            "Use less spacing for related elements",
            "Maintain consistent vertical rhythm"
        ]
    }

    # Component guidelines
    style_guide["component_guidelines"] = {
        "buttons": {
            "minimum_touch_target": "44px",
            "border_radius": "6px",
            "padding": "12px 24px",
            "states": ["default", "hover", "active", "disabled", "loading"]
        },
        "form_elements": {
            "input_height": "48px",
            "border_radius": "4px",
            "focus_outline": "2px solid primary-color",
            "error_color": "#dc3545"
        },
        "cards": {
            "border_radius": "8px",
            "shadow": "0 2px 4px rgba(0,0,0,0.1)",
            "padding": "24px"
        }
    }

    # Interaction patterns
    style_guide["interaction_patterns"] = {
        "hover_effects": "Smooth transitions (200ms ease)",
        "loading_states": "Show progress for operations > 1 second",
        "error_handling": "Clear, actionable error messages",
        "success_feedback": "Confirm successful actions",
        "navigation": "Consistent placement and styling"
    }

    # Accessibility standards
    style_guide["accessibility_standards"] = {
        "color_contrast": "Minimum 4.5:1 for normal text, 3:1 for large text",
        "keyboard_navigation": "All interactive elements accessible via keyboard",
        "alt_text": "Meaningful descriptions for images",
        "aria_labels": "Proper labels for screen readers",
        "focus_indicators": "Visible focus states for all interactive elements"
    }

    return style_guide


async def analyze_layout_patterns(interface_files: List[str] = None) -> Dict[str, Any]:
    """
    Analyze layout patterns and grid usage across interface files.

    Args:
        interface_files: Interface files to analyze

    Returns:
        Dict containing layout analysis
    """
    if interface_files is None:
        interface_files = []

    layout_analysis = {
        "layout_consistency": 0,
        "grid_usage": {},
        "spacing_patterns": {},
        "responsive_design": {},
        "issues_found": [],
        "recommendations": []
    }

    grid_patterns = []
    spacing_values = []
    responsive_breakpoints = []

    for file_path in interface_files:
        try:
            path = Path(file_path)
            if path.exists():
                content = path.read_text()

                # Look for CSS Grid usage
                if re.search(r"display:\s*grid", content, re.IGNORECASE):
                    grid_patterns.append("CSS Grid")

                # Look for Flexbox usage
                if re.search(r"display:\s*flex", content, re.IGNORECASE):
                    grid_patterns.append("Flexbox")

                # Extract spacing values
                margin_matches = re.findall(r"margin[^:]*:\s*([^;]+)", content, re.IGNORECASE)
                padding_matches = re.findall(r"padding[^:]*:\s*([^;]+)", content, re.IGNORECASE)
                spacing_values.extend(margin_matches + padding_matches)

                # Look for responsive breakpoints
                media_queries = re.findall(r"@media[^{]*\([^)]*([0-9]+px)[^)]*\)", content, re.IGNORECASE)
                responsive_breakpoints.extend(media_queries)

        except Exception:
            continue

    # Analyze patterns
    unique_spacing = list(set([s.strip() for s in spacing_values]))
    unique_breakpoints = list(set(responsive_breakpoints))

    layout_analysis["grid_usage"] = {
        "css_grid_usage": grid_patterns.count("CSS Grid"),
        "flexbox_usage": grid_patterns.count("Flexbox"),
        "layout_methods": list(set(grid_patterns))
    }

    layout_analysis["spacing_patterns"] = {
        "unique_values": len(unique_spacing),
        "common_values": unique_spacing[:10],
        "consistency_score": _calculate_spacing_consistency(unique_spacing)
    }

    layout_analysis["responsive_design"] = {
        "breakpoints_found": len(unique_breakpoints),
        "common_breakpoints": unique_breakpoints[:5]
    }

    # Identify issues
    if len(unique_spacing) > 15:
        layout_analysis["issues_found"].append({
            "category": "spacing_consistency",
            "severity": "medium",
            "description": f"Too many spacing values ({len(unique_spacing)})",
            "recommendation": "Establish consistent spacing scale"
        })

    if len(unique_breakpoints) == 0:
        layout_analysis["issues_found"].append({
            "category": "responsive_design",
            "severity": "high",
            "description": "No responsive breakpoints found",
            "recommendation": "Implement responsive design for mobile compatibility"
        })

    # Calculate consistency score
    spacing_penalty = max(0, (len(unique_spacing) - 8) * 5)
    layout_analysis["layout_consistency"] = max(0, 100 - spacing_penalty)

    # Generate recommendations
    layout_analysis["recommendations"] = [
        "Establish consistent spacing scale (8px base unit recommended)",
        "Use CSS Grid or Flexbox for layout consistency",
        "Implement responsive design with standard breakpoints",
        "Maintain consistent margins and padding patterns",
        "Consider using a CSS framework or design tokens"
    ]

    return layout_analysis


# Helper functions
async def _analyze_color_properties(color: str) -> Optional[Dict[str, Any]]:
    """Analyze properties of a single color."""
    try:
        # Convert color to RGB for analysis
        rgb = _color_to_rgb(color)
        if not rgb:
            return None

        r, g, b = rgb

        # Convert to HSV for color analysis
        h, s, v = colorsys.rgb_to_hsv(r/255, g/255, b/255)

        return {
            "original": color,
            "rgb": rgb,
            "hsv": (round(h*360), round(s*100), round(v*100)),
            "brightness": round((r + g + b) / 3),
            "is_light": (r + g + b) / 3 > 127,
            "is_saturated": s > 0.5
        }
    except:
        return None


def _color_to_rgb(color: str) -> Optional[Tuple[int, int, int]]:
    """Convert color string to RGB tuple."""
    try:
        # Handle hex colors
        if color.startswith('#'):
            color = color[1:]
            if len(color) == 3:
                color = ''.join([c*2 for c in color])
            if len(color) == 6:
                return tuple(int(color[i:i+2], 16) for i in (0, 2, 4))

        # Handle rgb colors
        if color.startswith('rgb'):
            rgb_match = re.search(r'rgb\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', color)
            if rgb_match:
                return tuple(int(x) for x in rgb_match.groups())
    except:
        pass

    return None


def _calculate_contrast_ratio(color1: Dict[str, Any], color2: Dict[str, Any]) -> float:
    """Calculate contrast ratio between two colors."""
    try:
        rgb1 = color1.get("rgb", (0, 0, 0))
        rgb2 = color2.get("rgb", (255, 255, 255))

        # Calculate relative luminance
        def relative_luminance(rgb):
            r, g, b = [x/255.0 for x in rgb]
            # Apply gamma correction
            r = r/12.92 if r <= 0.03928 else pow((r + 0.055)/1.055, 2.4)
            g = g/12.92 if g <= 0.03928 else pow((g + 0.055)/1.055, 2.4)
            b = b/12.92 if b <= 0.03928 else pow((b + 0.055)/1.055, 2.4)
            return 0.2126 * r + 0.7152 * g + 0.0722 * b

        l1 = relative_luminance(rgb1)
        l2 = relative_luminance(rgb2)

        # Ensure l1 is the lighter color
        if l1 < l2:
            l1, l2 = l2, l1

        return (l1 + 0.05) / (l2 + 0.05)
    except:
        return 1.0


def _calculate_color_harmony(colors: List[Dict[str, Any]]) -> int:
    """Calculate color harmony score based on HSV relationships."""
    if len(colors) < 2:
        return 50

    try:
        hues = [color["hsv"][0] for color in colors if color.get("hsv")]
        if not hues:
            return 50

        # Check for common color harmonies
        harmony_score = 50

        # Complementary (180° apart)
        for i, h1 in enumerate(hues):
            for h2 in hues[i+1:]:
                diff = abs(h1 - h2)
                if abs(diff - 180) < 15:  # Allow 15° tolerance
                    harmony_score += 15

        # Triadic (120° apart)
        if len(hues) >= 3:
            for i, h1 in enumerate(hues):
                for j, h2 in enumerate(hues[i+1:], i+1):
                    for h3 in hues[j+1:]:
                        if abs(abs(h1-h2) - 120) < 15 and abs(abs(h2-h3) - 120) < 15:
                            harmony_score += 20

        # Analogous (close together)
        close_colors = 0
        for i, h1 in enumerate(hues):
            for h2 in hues[i+1:]:
                if abs(h1 - h2) < 30:
                    close_colors += 1

        if close_colors >= 2:
            harmony_score += 10

        return min(100, harmony_score)
    except:
        return 50


def _calculate_consistency_score(font_sizes: List[str], colors: List[str]) -> int:
    """Calculate consistency score based on font and color variety."""
    font_penalty = max(0, (len(font_sizes) - 6) * 5)
    color_penalty = max(0, (len(colors) - 10) * 3)
    return max(0, 100 - font_penalty - color_penalty)


def _calculate_spacing_consistency(spacing_values: List[str]) -> int:
    """Calculate spacing consistency score."""
    if not spacing_values:
        return 50

    # Extract numeric values
    numeric_values = []
    for value in spacing_values:
        numbers = re.findall(r'\d+', value)
        numeric_values.extend([int(n) for n in numbers])

    if not numeric_values:
        return 50

    # Check if values follow a consistent scale (multiples of 4 or 8)
    consistent_8px = sum(1 for v in numeric_values if v % 8 == 0)
    consistent_4px = sum(1 for v in numeric_values if v % 4 == 0)

    consistency_8 = (consistent_8px / len(numeric_values)) * 100
    consistency_4 = (consistent_4px / len(numeric_values)) * 100

    return round(max(consistency_8, consistency_4))


def _generate_palette_suggestions(colors: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Generate improved color palette suggestions."""
    suggestions = {
        "primary_palette": [],
        "accessibility_improvements": [],
        "harmony_suggestions": []
    }

    if not colors:
        return suggestions

    # Sort colors by brightness for primary palette
    sorted_colors = sorted(colors, key=lambda x: x.get("brightness", 0))

    # Suggest primary colors (darkest, middle, lightest)
    if len(sorted_colors) >= 3:
        suggestions["primary_palette"] = [
            {"role": "primary", "color": sorted_colors[-1]["original"], "usage": "Main brand color"},
            {"role": "secondary", "color": sorted_colors[len(sorted_colors)//2]["original"], "usage": "Supporting actions"},
            {"role": "accent", "color": sorted_colors[0]["original"], "usage": "Highlights and calls-to-action"}
        ]

    # Accessibility improvements
    light_colors = [c for c in colors if c.get("is_light", True)]
    dark_colors = [c for c in colors if not c.get("is_light", True)]

    if len(light_colors) < 2 or len(dark_colors) < 2:
        suggestions["accessibility_improvements"].append(
            "Add both light and dark color variations for better contrast options"
        )

    suggestions["harmony_suggestions"] = [
        "Consider using a 60-30-10 color distribution rule",
        "Test color combinations with accessibility tools",
        "Create tints and shades of primary colors for consistency",
        "Use neutral colors (grays) for balance"
    ]

    return suggestions