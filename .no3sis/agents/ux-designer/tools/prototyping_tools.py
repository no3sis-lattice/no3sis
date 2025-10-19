"""
Prototyping and design system creation tools.
"""

import json
from typing import Dict, List, Any, Optional
from dataclasses import dataclass


@dataclass
class UserStory:
    """Represents a user story for design requirements."""
    title: str
    as_a: str
    i_want: str
    so_that: str
    acceptance_criteria: List[str]
    priority: str  # high, medium, low
    complexity: str  # simple, medium, complex


async def generate_wireframes(
    user_requirements: List[str],
    page_type: str = "web_page",
    fidelity: str = "low"
) -> Dict[str, Any]:
    """
    Generate wireframe specifications based on user requirements.

    Args:
        user_requirements: List of functional requirements
        page_type: Type of interface (web_page, mobile_app, dashboard)
        fidelity: Wireframe detail level (low, medium, high)

    Returns:
        Dict containing wireframe specifications
    """
    wireframe_specs = {
        "page_type": page_type,
        "fidelity_level": fidelity,
        "layout_structure": {},
        "components": [],
        "user_flow": [],
        "annotations": [],
        "responsive_considerations": {}
    }

    # Define layout structure based on page type
    if page_type == "web_page":
        wireframe_specs["layout_structure"] = {
            "header": {
                "height": "80px",
                "elements": ["logo", "navigation", "user_menu"],
                "priority": "high"
            },
            "main_content": {
                "layout": "single_column" if len(user_requirements) <= 3 else "multi_column",
                "sections": _derive_sections_from_requirements(user_requirements),
                "priority": "critical"
            },
            "sidebar": {
                "width": "300px",
                "show_when": len(user_requirements) > 5,
                "elements": ["filters", "secondary_actions", "context_info"],
                "priority": "medium"
            },
            "footer": {
                "height": "120px",
                "elements": ["links", "copyright", "social"],
                "priority": "low"
            }
        }

    elif page_type == "mobile_app":
        wireframe_specs["layout_structure"] = {
            "status_bar": {"height": "44px", "priority": "system"},
            "header": {
                "height": "64px",
                "elements": ["back_button", "title", "action_button"],
                "priority": "high"
            },
            "main_content": {
                "layout": "scroll_view",
                "sections": _derive_mobile_sections(user_requirements),
                "priority": "critical"
            },
            "tab_bar": {
                "height": "80px",
                "show_when": len(user_requirements) > 3,
                "elements": ["tab_items"],
                "priority": "high"
            }
        }

    elif page_type == "dashboard":
        wireframe_specs["layout_structure"] = {
            "header": {
                "height": "60px",
                "elements": ["breadcrumbs", "search", "notifications"],
                "priority": "high"
            },
            "sidebar": {
                "width": "240px",
                "elements": ["menu", "user_info"],
                "priority": "high"
            },
            "main_dashboard": {
                "layout": "grid",
                "grid_columns": 12,
                "sections": _derive_dashboard_widgets(user_requirements),
                "priority": "critical"
            }
        }

    # Generate components based on fidelity
    if fidelity == "low":
        wireframe_specs["components"] = _generate_low_fi_components(user_requirements)
    elif fidelity == "medium":
        wireframe_specs["components"] = _generate_medium_fi_components(user_requirements)
    else:  # high fidelity
        wireframe_specs["components"] = _generate_high_fi_components(user_requirements)

    # Create user flow
    wireframe_specs["user_flow"] = _generate_user_flow(user_requirements, page_type)

    # Add annotations
    wireframe_specs["annotations"] = [
        "Primary user actions should be most prominent",
        "Group related functionality together",
        "Ensure clear visual hierarchy",
        "Consider mobile-first responsive design",
        "Include loading and error states"
    ]

    # Responsive considerations
    wireframe_specs["responsive_considerations"] = {
        "mobile": "Stack elements vertically, collapse navigation",
        "tablet": "Adjust grid to 2-column layout",
        "desktop": "Full multi-column layout with sidebar"
    }

    return wireframe_specs


async def create_user_stories(
    project_description: str,
    user_personas: List[Dict[str, Any]] = None
) -> Dict[str, Any]:
    """
    Create user stories based on project description and personas.

    Args:
        project_description: Description of the project and its goals
        user_personas: List of user persona data

    Returns:
        Dict containing generated user stories
    """
    if user_personas is None:
        user_personas = [{"name": "Primary User", "role": "End User"}]

    user_stories_result = {
        "total_stories": 0,
        "stories_by_priority": {"high": [], "medium": [], "low": []},
        "stories_by_persona": {},
        "epic_groupings": {},
        "story_map": {}
    }

    # Generate stories for each persona
    for persona in user_personas:
        persona_name = persona.get("name", "User")
        persona_role = persona.get("role", "User")

        persona_stories = []

        # Core functionality stories
        core_stories = [
            UserStory(
                title="User Registration",
                as_a=persona_role,
                i_want="to create an account",
                so_that="I can access personalized features",
                acceptance_criteria=[
                    "User can enter email and password",
                    "System validates input format",
                    "Confirmation email is sent",
                    "User can activate account"
                ],
                priority="high",
                complexity="medium"
            ),
            UserStory(
                title="User Authentication",
                as_a=persona_role,
                i_want="to log into my account securely",
                so_that="I can access my personal data",
                acceptance_criteria=[
                    "User can enter credentials",
                    "System authenticates user",
                    "Failed attempts are handled gracefully",
                    "Remember me option available"
                ],
                priority="high",
                complexity="simple"
            ),
            UserStory(
                title="Profile Management",
                as_a=persona_role,
                i_want="to update my profile information",
                so_that="my account reflects current information",
                acceptance_criteria=[
                    "User can view current profile",
                    "User can edit profile fields",
                    "Changes are saved successfully",
                    "User receives confirmation"
                ],
                priority="medium",
                complexity="simple"
            )
        ]

        # Add project-specific stories
        if "e-commerce" in project_description.lower() or "shop" in project_description.lower():
            ecommerce_stories = [
                UserStory(
                    title="Product Search",
                    as_a="Customer",
                    i_want="to search for products",
                    so_that="I can find items I want to purchase",
                    acceptance_criteria=[
                        "Search bar is prominently displayed",
                        "Search results are relevant",
                        "Filters are available",
                        "Results load quickly"
                    ],
                    priority="high",
                    complexity="medium"
                ),
                UserStory(
                    title="Add to Cart",
                    as_a="Customer",
                    i_want="to add products to my shopping cart",
                    so_that="I can purchase multiple items together",
                    acceptance_criteria=[
                        "Add to cart button is visible",
                        "Cart count updates immediately",
                        "User can view cart contents",
                        "Items persist in cart"
                    ],
                    priority="high",
                    complexity="simple"
                )
            ]
            core_stories.extend(ecommerce_stories)

        elif "dashboard" in project_description.lower() or "analytics" in project_description.lower():
            dashboard_stories = [
                UserStory(
                    title="Data Visualization",
                    as_a="Analyst",
                    i_want="to view data in charts and graphs",
                    so_that="I can understand trends and patterns",
                    acceptance_criteria=[
                        "Charts load with real data",
                        "Multiple chart types available",
                        "Data updates automatically",
                        "Charts are interactive"
                    ],
                    priority="high",
                    complexity="complex"
                ),
                UserStory(
                    title="Custom Reports",
                    as_a="Manager",
                    i_want="to generate custom reports",
                    so_that="I can share insights with stakeholders",
                    acceptance_criteria=[
                        "Report builder is intuitive",
                        "Multiple export formats available",
                        "Reports can be scheduled",
                        "Data is accurate"
                    ],
                    priority="medium",
                    complexity="complex"
                )
            ]
            core_stories.extend(dashboard_stories)

        persona_stories.extend(core_stories)
        user_stories_result["stories_by_persona"][persona_name] = persona_stories

        # Categorize by priority
        for story in persona_stories:
            priority_key = story.priority
            user_stories_result["stories_by_priority"][priority_key].append(story)

    # Count total stories
    total_count = sum(len(stories) for stories in user_stories_result["stories_by_priority"].values())
    user_stories_result["total_stories"] = total_count

    # Create epic groupings
    user_stories_result["epic_groupings"] = {
        "User Management": ["User Registration", "User Authentication", "Profile Management"],
        "Core Features": [s.title for s in core_stories if s.title not in ["User Registration", "User Authentication", "Profile Management"]],
        "Advanced Features": []
    }

    # Create story map (simplified)
    user_stories_result["story_map"] = {
        "backbone": ["User Journey", "Core Workflow", "Supporting Features"],
        "walking_skeleton": [s.title for s in core_stories if s.priority == "high"],
        "release_1": [s.title for s in core_stories if s.priority in ["high", "medium"]]
    }

    # Convert UserStory objects to dicts for JSON serialization
    for priority, stories in user_stories_result["stories_by_priority"].items():
        user_stories_result["stories_by_priority"][priority] = [
            {
                "title": s.title,
                "as_a": s.as_a,
                "i_want": s.i_want,
                "so_that": s.so_that,
                "acceptance_criteria": s.acceptance_criteria,
                "priority": s.priority,
                "complexity": s.complexity
            }
            for s in stories
        ]

    for persona, stories in user_stories_result["stories_by_persona"].items():
        user_stories_result["stories_by_persona"][persona] = [
            {
                "title": s.title,
                "as_a": s.as_a,
                "i_want": s.i_want,
                "so_that": s.so_that,
                "acceptance_criteria": s.acceptance_criteria,
                "priority": s.priority,
                "complexity": s.complexity
            }
            for s in stories
        ]

    return user_stories_result


async def design_mockups(
    wireframe_data: Dict[str, Any],
    style_guide: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    Generate high-fidelity mockup specifications from wireframes.

    Args:
        wireframe_data: Wireframe specifications
        style_guide: Style guide with colors, typography, etc.

    Returns:
        Dict containing mockup specifications
    """
    if style_guide is None:
        style_guide = _get_default_style_guide()

    mockup_specs = {
        "visual_design": {},
        "component_library": {},
        "asset_requirements": [],
        "interaction_states": {},
        "responsive_layouts": {}
    }

    layout_structure = wireframe_data.get("layout_structure", {})

    # Apply visual design to layout
    mockup_specs["visual_design"] = {
        "color_scheme": style_guide.get("color_system", {}),
        "typography": style_guide.get("typography_system", {}),
        "spacing": style_guide.get("spacing_system", {}),
        "layout_enhancements": _enhance_layout_with_style(layout_structure, style_guide)
    }

    # Create detailed component specifications
    components = wireframe_data.get("components", [])
    mockup_specs["component_library"] = _create_component_specs(components, style_guide)

    # Define asset requirements
    mockup_specs["asset_requirements"] = [
        {"type": "icons", "style": "outline", "sizes": ["16px", "24px", "32px"]},
        {"type": "illustrations", "style": "modern", "contexts": ["empty_states", "onboarding"]},
        {"type": "images", "specs": "high_quality", "formats": ["webp", "png"]},
        {"type": "logo", "variants": ["horizontal", "vertical", "icon_only"]}
    ]

    # Define interaction states
    mockup_specs["interaction_states"] = {
        "buttons": {
            "default": {"background": style_guide.get("color_system", {}).get("primary", "#007bff")},
            "hover": {"background": _darken_color(style_guide.get("color_system", {}).get("primary", "#007bff"), 0.1)},
            "active": {"background": _darken_color(style_guide.get("color_system", {}).get("primary", "#007bff"), 0.2)},
            "disabled": {"background": "#6c757d", "opacity": 0.5}
        },
        "form_inputs": {
            "default": {"border": "1px solid #ced4da"},
            "focus": {"border": "2px solid " + style_guide.get("color_system", {}).get("primary", "#007bff")},
            "error": {"border": "2px solid #dc3545"},
            "success": {"border": "2px solid #28a745"}
        },
        "loading": {
            "spinner": {"color": style_guide.get("color_system", {}).get("primary", "#007bff")},
            "skeleton": {"background": "#f8f9fa", "animation": "pulse"}
        }
    }

    # Create responsive layout specifications
    mockup_specs["responsive_layouts"] = {
        "mobile": {
            "max_width": "768px",
            "layout": "single_column",
            "navigation": "hamburger_menu",
            "grid_columns": 1
        },
        "tablet": {
            "max_width": "1024px",
            "layout": "two_column",
            "navigation": "collapsed_sidebar",
            "grid_columns": 2
        },
        "desktop": {
            "min_width": "1025px",
            "layout": "multi_column",
            "navigation": "full_sidebar",
            "grid_columns": 3
        }
    }

    return mockup_specs


async def validate_interaction_patterns(
    interaction_specs: Dict[str, Any],
    usability_standards: List[str] = None
) -> Dict[str, Any]:
    """
    Validate interaction patterns against usability standards.

    Args:
        interaction_specs: Interaction pattern specifications
        usability_standards: List of standards to validate against

    Returns:
        Dict containing validation results
    """
    if usability_standards is None:
        usability_standards = ["wcag_2.1", "material_design", "ios_hig"]

    validation_results = {
        "overall_score": 0,
        "standard_compliance": {},
        "violations_found": [],
        "recommendations": [],
        "accessibility_score": 0
    }

    # Validate against each standard
    for standard in usability_standards:
        compliance_score = await _validate_against_standard(interaction_specs, standard)
        validation_results["standard_compliance"][standard] = compliance_score

    # Check for common interaction issues
    violations = []

    # Check touch target sizes
    buttons = interaction_specs.get("buttons", {})
    if buttons:
        default_button = buttons.get("default", {})
        if "min_height" not in default_button or int(default_button.get("min_height", "0").replace("px", "")) < 44:
            violations.append({
                "category": "touch_targets",
                "severity": "high",
                "description": "Button touch targets below 44px minimum",
                "recommendation": "Ensure all touch targets are minimum 44px for accessibility"
            })

    # Check for missing states
    required_states = ["default", "hover", "active", "disabled"]
    for component_type, states in interaction_specs.items():
        if isinstance(states, dict):
            missing_states = [state for state in required_states if state not in states]
            if missing_states:
                violations.append({
                    "category": "interaction_states",
                    "severity": "medium",
                    "description": f"{component_type} missing states: {missing_states}",
                    "recommendation": f"Add missing interaction states for {component_type}"
                })

    # Check loading states
    if "loading" not in interaction_specs:
        violations.append({
            "category": "loading_states",
            "severity": "medium",
            "description": "No loading states defined",
            "recommendation": "Define loading states for asynchronous operations"
        })

    validation_results["violations_found"] = violations

    # Calculate scores
    violation_penalty = len(violations) * 15
    validation_results["overall_score"] = max(0, 100 - violation_penalty)

    # Calculate accessibility score based on specific criteria
    accessibility_violations = [v for v in violations if v["category"] in ["touch_targets", "color_contrast", "keyboard_navigation"]]
    accessibility_penalty = len(accessibility_violations) * 20
    validation_results["accessibility_score"] = max(0, 100 - accessibility_penalty)

    # Generate recommendations
    recommendations = []
    if violations:
        recommendations.append("Address identified interaction pattern violations")

    recommendations.extend([
        "Test interactions with keyboard navigation",
        "Verify touch targets meet minimum size requirements",
        "Ensure consistent interaction patterns across components",
        "Provide clear feedback for all user actions",
        "Test with assistive technologies"
    ])

    validation_results["recommendations"] = recommendations

    return validation_results


async def generate_component_library(
    design_system: Dict[str, Any],
    component_types: List[str] = None
) -> Dict[str, Any]:
    """
    Generate comprehensive component library specifications.

    Args:
        design_system: Design system specifications
        component_types: List of component types to generate

    Returns:
        Dict containing component library specifications
    """
    if component_types is None:
        component_types = ["button", "input", "card", "modal", "dropdown", "navigation"]

    component_library = {
        "library_metadata": {
            "version": "1.0.0",
            "last_updated": "2024-01-01",
            "total_components": len(component_types)
        },
        "design_tokens": {},
        "components": {},
        "usage_guidelines": {},
        "accessibility_standards": {}
    }

    # Extract design tokens from design system
    component_library["design_tokens"] = {
        "colors": design_system.get("color_system", {}),
        "typography": design_system.get("typography_system", {}),
        "spacing": design_system.get("spacing_system", {}),
        "borders": {"radius": "6px", "width": "1px"},
        "shadows": {"small": "0 1px 3px rgba(0,0,0,0.1)", "medium": "0 4px 6px rgba(0,0,0,0.1)"}
    }

    # Generate component specifications
    for component_type in component_types:
        component_library["components"][component_type] = _generate_component_spec(
            component_type, component_library["design_tokens"]
        )

    # Usage guidelines
    component_library["usage_guidelines"] = {
        "when_to_use": "Component selection guidelines based on use case",
        "composition_rules": "How components work together",
        "customization_limits": "Approved ways to modify components",
        "responsive_behavior": "How components adapt to different screen sizes"
    }

    # Accessibility standards
    component_library["accessibility_standards"] = {
        "keyboard_navigation": "All components support keyboard interaction",
        "screen_reader_support": "Proper ARIA labels and roles implemented",
        "color_contrast": "All text meets WCAG AA contrast requirements",
        "focus_indicators": "Visible focus states for all interactive elements"
    }

    return component_library


async def create_design_system(
    brand_guidelines: Dict[str, Any] = None,
    technical_constraints: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    Create comprehensive design system specifications.

    Args:
        brand_guidelines: Brand identity guidelines
        technical_constraints: Technical implementation constraints

    Returns:
        Dict containing complete design system
    """
    if brand_guidelines is None:
        brand_guidelines = {}
    if technical_constraints is None:
        technical_constraints = {}

    design_system = {
        "foundation": {},
        "components": {},
        "patterns": {},
        "guidelines": {},
        "implementation": {}
    }

    # Foundation layer
    design_system["foundation"] = {
        "color_system": {
            "primary": brand_guidelines.get("primary_color", "#007bff"),
            "secondary": brand_guidelines.get("secondary_color", "#6c757d"),
            "accent": brand_guidelines.get("accent_color", "#28a745"),
            "semantic_colors": {
                "success": "#28a745",
                "warning": "#ffc107",
                "danger": "#dc3545",
                "info": "#17a2b8"
            },
            "neutral_colors": {
                "white": "#ffffff",
                "gray_100": "#f8f9fa",
                "gray_200": "#e9ecef",
                "gray_500": "#6c757d",
                "gray_900": "#212529",
                "black": "#000000"
            }
        },
        "typography": {
            "font_families": {
                "primary": brand_guidelines.get("primary_font", "Inter, system-ui, sans-serif"),
                "secondary": brand_guidelines.get("secondary_font", "Georgia, serif"),
                "monospace": "Monaco, Consolas, monospace"
            },
            "type_scale": {
                "xs": "0.75rem",
                "sm": "0.875rem",
                "base": "1rem",
                "lg": "1.125rem",
                "xl": "1.25rem",
                "2xl": "1.5rem",
                "3xl": "1.875rem",
                "4xl": "2.25rem"
            },
            "line_heights": {
                "tight": 1.2,
                "normal": 1.5,
                "relaxed": 1.6,
                "loose": 2.0
            }
        },
        "spacing": {
            "base_unit": "8px",
            "scale": ["4px", "8px", "16px", "24px", "32px", "48px", "64px", "96px"]
        },
        "layout": {
            "grid_columns": 12,
            "container_max_width": "1200px",
            "breakpoints": {
                "sm": "640px",
                "md": "768px",
                "lg": "1024px",
                "xl": "1280px"
            }
        }
    }

    # Component specifications
    design_system["components"] = {
        "forms": {
            "input_height": "48px",
            "border_radius": "6px",
            "focus_outline": "2px solid primary",
            "error_styling": "border: 2px solid danger"
        },
        "buttons": {
            "min_height": "44px",
            "border_radius": "6px",
            "padding": "12px 24px",
            "font_weight": "500"
        },
        "cards": {
            "border_radius": "8px",
            "shadow": "0 2px 4px rgba(0,0,0,0.1)",
            "padding": "24px"
        }
    }

    # Design patterns
    design_system["patterns"] = {
        "navigation": {
            "primary_navigation": "Horizontal top bar for main sections",
            "secondary_navigation": "Vertical sidebar for sub-sections",
            "breadcrumbs": "Show path for deep hierarchies"
        },
        "content_organization": {
            "information_hierarchy": "Use heading levels consistently",
            "content_grouping": "Group related content with cards or sections",
            "progressive_disclosure": "Show details on demand"
        },
        "feedback": {
            "loading_states": "Show progress for operations > 1 second",
            "success_feedback": "Confirm completed actions",
            "error_handling": "Clear, actionable error messages"
        }
    }

    # Usage guidelines
    design_system["guidelines"] = {
        "accessibility": {
            "color_contrast": "Minimum 4.5:1 for normal text",
            "keyboard_navigation": "All interactive elements accessible",
            "screen_readers": "Proper semantic markup and ARIA labels"
        },
        "responsive_design": {
            "mobile_first": "Design for mobile, enhance for larger screens",
            "touch_targets": "Minimum 44px for touch interfaces",
            "content_priority": "Most important content first"
        },
        "performance": {
            "image_optimization": "Use appropriate formats and sizes",
            "critical_css": "Inline critical styles",
            "loading_optimization": "Lazy load non-critical content"
        }
    }

    # Implementation guidance
    design_system["implementation"] = {
        "css_methodology": technical_constraints.get("css_approach", "CSS-in-JS"),
        "component_framework": technical_constraints.get("framework", "React"),
        "build_tools": technical_constraints.get("build_tools", ["Vite", "PostCSS"]),
        "testing_strategy": "Visual regression testing for components",
        "documentation_tools": "Storybook for component documentation"
    }

    return design_system


# Helper functions
def _derive_sections_from_requirements(requirements: List[str]) -> List[Dict[str, Any]]:
    """Derive content sections from user requirements."""
    sections = []
    for i, req in enumerate(requirements[:5]):  # Limit to 5 sections
        sections.append({
            "name": f"section_{i+1}",
            "content_type": _infer_content_type(req),
            "priority": "high" if i < 2 else "medium",
            "estimated_height": "300px"
        })
    return sections


def _derive_mobile_sections(requirements: List[str]) -> List[Dict[str, Any]]:
    """Derive mobile-specific sections."""
    return [
        {
            "name": f"mobile_section_{i+1}",
            "content_type": _infer_content_type(req),
            "full_width": True,
            "stack_order": i+1
        }
        for i, req in enumerate(requirements[:3])
    ]


def _derive_dashboard_widgets(requirements: List[str]) -> List[Dict[str, Any]]:
    """Derive dashboard widgets from requirements."""
    widgets = []
    for req in requirements[:6]:  # Max 6 widgets
        widgets.append({
            "type": _infer_widget_type(req),
            "size": "medium",
            "data_source": "api",
            "refresh_rate": "5min"
        })
    return widgets


def _infer_content_type(requirement: str) -> str:
    """Infer content type from requirement text."""
    req_lower = requirement.lower()
    if "form" in req_lower or "input" in req_lower:
        return "form"
    elif "list" in req_lower or "table" in req_lower:
        return "data_list"
    elif "chart" in req_lower or "graph" in req_lower:
        return "visualization"
    else:
        return "content_block"


def _infer_widget_type(requirement: str) -> str:
    """Infer widget type for dashboard."""
    req_lower = requirement.lower()
    if "chart" in req_lower or "graph" in req_lower:
        return "chart_widget"
    elif "metric" in req_lower or "kpi" in req_lower:
        return "metric_widget"
    elif "list" in req_lower:
        return "list_widget"
    else:
        return "info_widget"


def _generate_low_fi_components(requirements: List[str]) -> List[Dict[str, Any]]:
    """Generate low-fidelity component specifications."""
    return [
        {"type": "text_block", "detail_level": "placeholder"},
        {"type": "button", "detail_level": "box_outline"},
        {"type": "form_field", "detail_level": "input_outline"},
        {"type": "navigation", "detail_level": "menu_structure"}
    ]


def _generate_medium_fi_components(requirements: List[str]) -> List[Dict[str, Any]]:
    """Generate medium-fidelity component specifications."""
    return [
        {"type": "text_block", "detail_level": "lorem_ipsum"},
        {"type": "button", "detail_level": "labeled_with_style"},
        {"type": "form_field", "detail_level": "typed_inputs"},
        {"type": "navigation", "detail_level": "labeled_menu_items"},
        {"type": "image_placeholder", "detail_level": "sized_boxes"}
    ]


def _generate_high_fi_components(requirements: List[str]) -> List[Dict[str, Any]]:
    """Generate high-fidelity component specifications."""
    return [
        {"type": "text_block", "detail_level": "actual_content"},
        {"type": "button", "detail_level": "final_styling"},
        {"type": "form_field", "detail_level": "validation_states"},
        {"type": "navigation", "detail_level": "interactive_states"},
        {"type": "images", "detail_level": "actual_or_representative"},
        {"type": "icons", "detail_level": "icon_library"}
    ]


def _generate_user_flow(requirements: List[str], page_type: str) -> List[Dict[str, str]]:
    """Generate user flow steps."""
    if page_type == "mobile_app":
        return [
            {"step": 1, "action": "App launch", "screen": "splash"},
            {"step": 2, "action": "User authentication", "screen": "login"},
            {"step": 3, "action": "Main functionality", "screen": "primary"},
            {"step": 4, "action": "Task completion", "screen": "confirmation"}
        ]
    else:
        return [
            {"step": 1, "action": "Page load", "screen": "landing"},
            {"step": 2, "action": "User interaction", "screen": "interface"},
            {"step": 3, "action": "Task completion", "screen": "result"}
        ]


def _get_default_style_guide() -> Dict[str, Any]:
    """Get default style guide when none provided."""
    return {
        "color_system": {
            "primary": "#007bff",
            "secondary": "#6c757d",
            "accent": "#28a745"
        },
        "typography_system": {
            "font_families": {
                "primary": "Inter, sans-serif"
            }
        },
        "spacing_system": {
            "base_unit": "8px"
        }
    }


def _enhance_layout_with_style(layout: Dict[str, Any], style_guide: Dict[str, Any]) -> Dict[str, Any]:
    """Enhance layout structure with visual design elements."""
    enhanced = {}
    colors = style_guide.get("color_system", {})

    for section_name, section_data in layout.items():
        enhanced[section_name] = {
            **section_data,
            "background_color": _get_section_background_color(section_name, colors),
            "text_color": _get_section_text_color(section_name, colors),
            "border": _get_section_border(section_name)
        }

    return enhanced


def _create_component_specs(components: List[Dict[str, Any]], style_guide: Dict[str, Any]) -> Dict[str, Any]:
    """Create detailed component specifications with styling."""
    specs = {}

    for component in components:
        comp_type = component.get("type", "unknown")
        specs[comp_type] = {
            "visual_properties": _get_component_visual_props(comp_type, style_guide),
            "interaction_states": _get_component_states(comp_type),
            "responsive_behavior": _get_component_responsive_behavior(comp_type)
        }

    return specs


def _get_section_background_color(section_name: str, colors: Dict[str, str]) -> str:
    """Get appropriate background color for section."""
    if section_name == "header":
        return colors.get("primary", "#007bff")
    elif section_name == "footer":
        return colors.get("secondary", "#6c757d")
    else:
        return "#ffffff"


def _get_section_text_color(section_name: str, colors: Dict[str, str]) -> str:
    """Get appropriate text color for section."""
    if section_name in ["header", "footer"]:
        return "#ffffff"
    else:
        return "#212529"


def _get_section_border(section_name: str) -> str:
    """Get border specification for section."""
    if section_name == "sidebar":
        return "1px solid #e9ecef"
    else:
        return "none"


def _get_component_visual_props(comp_type: str, style_guide: Dict[str, Any]) -> Dict[str, Any]:
    """Get visual properties for component type."""
    colors = style_guide.get("color_system", {})

    if comp_type == "button":
        return {
            "background": colors.get("primary", "#007bff"),
            "color": "#ffffff",
            "border": "none",
            "border_radius": "6px",
            "padding": "12px 24px"
        }
    elif comp_type == "form_field":
        return {
            "background": "#ffffff",
            "border": "1px solid #ced4da",
            "border_radius": "4px",
            "padding": "12px"
        }
    else:
        return {"background": "#ffffff"}


def _get_component_states(comp_type: str) -> Dict[str, Any]:
    """Get interaction states for component type."""
    if comp_type == "button":
        return {
            "default": {"opacity": 1},
            "hover": {"opacity": 0.9},
            "active": {"opacity": 0.8},
            "disabled": {"opacity": 0.5}
        }
    else:
        return {}


def _get_component_responsive_behavior(comp_type: str) -> Dict[str, str]:
    """Get responsive behavior for component type."""
    return {
        "mobile": "Stack vertically, full width",
        "tablet": "Partial width, maintain proportions",
        "desktop": "Original layout"
    }


def _darken_color(color: str, amount: float) -> str:
    """Darken a color by specified amount."""
    # Simple implementation - in real system would use proper color manipulation
    return color  # Return original for now


async def _validate_against_standard(interaction_specs: Dict[str, Any], standard: str) -> int:
    """Validate interaction patterns against specific standard."""
    # Simplified validation - real implementation would check specific guidelines
    base_score = 75

    if standard == "wcag_2.1":
        # Check for accessibility compliance
        if "keyboard_navigation" in interaction_specs:
            base_score += 10
        if "screen_reader_support" in interaction_specs:
            base_score += 10

    elif standard == "material_design":
        # Check for material design compliance
        if "elevation" in interaction_specs or "shadow" in str(interaction_specs):
            base_score += 10

    elif standard == "ios_hig":
        # Check for iOS Human Interface Guidelines compliance
        if "touch_targets" in interaction_specs:
            base_score += 10

    return min(100, base_score)


def _generate_component_spec(component_type: str, design_tokens: Dict[str, Any]) -> Dict[str, Any]:
    """Generate specification for a component type."""
    base_spec = {
        "description": f"Standard {component_type} component",
        "props": [],
        "variants": [],
        "states": ["default"],
        "accessibility": {}
    }

    if component_type == "button":
        base_spec.update({
            "props": ["label", "variant", "size", "disabled", "loading"],
            "variants": ["primary", "secondary", "outline"],
            "states": ["default", "hover", "active", "disabled", "loading"],
            "accessibility": {
                "role": "button",
                "keyboard": "Space, Enter",
                "aria_attributes": ["aria-label", "aria-disabled"]
            }
        })

    elif component_type == "input":
        base_spec.update({
            "props": ["value", "placeholder", "type", "disabled", "error"],
            "variants": ["text", "email", "password", "number"],
            "states": ["default", "focus", "error", "disabled"],
            "accessibility": {
                "role": "textbox",
                "keyboard": "Standard text input",
                "aria_attributes": ["aria-label", "aria-describedby", "aria-invalid"]
            }
        })

    return base_spec