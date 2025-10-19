"""
User research and persona analysis tools.
"""

import json
from typing import Dict, List, Any, Optional
from dataclasses import dataclass


@dataclass
class UserPersona:
    """Represents a user persona with demographics and behavior patterns."""
    name: str
    age_range: str
    occupation: str
    goals: List[str]
    pain_points: List[str]
    tech_comfort: str
    preferred_devices: List[str]
    behaviors: List[str]


async def conduct_user_research(
    research_type: str = "user_interview",
    target_audience: str = "general_users",
    research_goals: List[str] = None
) -> Dict[str, Any]:
    """
    Conduct structured user research and analysis.

    Args:
        research_type: Type of research (user_interview, survey, usability_test, analytics)
        target_audience: Target user group description
        research_goals: List of research objectives

    Returns:
        Dict containing research methodology and expected outcomes
    """
    if research_goals is None:
        research_goals = ["understand_user_needs", "identify_pain_points", "validate_assumptions"]

    research_plan = {
        "research_type": research_type,
        "target_audience": target_audience,
        "methodology": {},
        "questions": [],
        "expected_deliverables": [],
        "timeline": {},
        "success_criteria": []
    }

    # Define methodology based on research type
    if research_type == "user_interview":
        research_plan["methodology"] = {
            "approach": "Semi-structured interviews",
            "participant_count": "8-12 participants",
            "session_duration": "45-60 minutes",
            "format": "One-on-one interviews",
            "recording": "Audio/video with consent",
            "analysis_method": "Thematic analysis"
        }

        research_plan["questions"] = [
            "Tell me about your current workflow/process",
            "What are your biggest challenges with [current solution]?",
            "Walk me through how you typically [perform key task]",
            "What would an ideal solution look like to you?",
            "How do you currently work around existing limitations?",
            "What tools do you use daily for [relevant tasks]?",
            "Describe a recent frustrating experience with [domain]",
            "How important is [specific feature] to your work?",
            "What would convince you to try a new solution?",
            "How do you typically learn new software/tools?"
        ]

    elif research_type == "survey":
        research_plan["methodology"] = {
            "approach": "Online survey",
            "participant_count": "100-500 responses",
            "estimated_completion": "10-15 minutes",
            "distribution": "Email, social media, targeted ads",
            "incentive": "Entry into prize draw",
            "analysis_method": "Statistical analysis"
        }

        research_plan["questions"] = [
            "What is your age range?",
            "How would you describe your role/occupation?",
            "How often do you [perform key activity]?",
            "Rate your satisfaction with current solutions (1-10)",
            "What features are most important to you? (rank order)",
            "What devices do you primarily use?",
            "How comfortable are you with technology? (1-10)",
            "What's your biggest pain point with [current process]?",
            "How much would you pay for an ideal solution?",
            "Where do you typically discover new tools/software?"
        ]

    elif research_type == "usability_test":
        research_plan["methodology"] = {
            "approach": "Moderated usability testing",
            "participant_count": "5-8 participants",
            "session_duration": "60-90 minutes",
            "format": "Think-aloud protocol",
            "environment": "Remote or in-person lab",
            "analysis_method": "Task success rate and error analysis"
        }

        research_plan["questions"] = [
            "Please complete [specific task] as you normally would",
            "What are you thinking as you look at this screen?",
            "What would you expect to happen if you clicked here?",
            "How does this compare to tools you currently use?",
            "What information are you looking for right now?",
            "Is there anything confusing or unclear on this page?",
            "How would you recover from this error?",
            "On a scale of 1-10, how difficult was this task?",
            "What would you change about this process?",
            "Would you use this feature in your daily work?"
        ]

    elif research_type == "analytics":
        research_plan["methodology"] = {
            "approach": "Data analysis and user behavior tracking",
            "data_sources": "Web analytics, app analytics, user logs",
            "timeframe": "3-6 months of data",
            "key_metrics": "User flows, conversion rates, drop-off points",
            "tools": "Google Analytics, Mixpanel, Hotjar",
            "analysis_method": "Quantitative analysis with statistical significance testing"
        }

        research_plan["questions"] = [
            "What are the most common user paths through the application?",
            "Where do users typically drop off in key workflows?",
            "Which features are used most/least frequently?",
            "What devices and browsers are most common?",
            "How long do users typically spend on each page/screen?",
            "What search terms do users enter most often?",
            "Which error messages appear most frequently?",
            "How do user behaviors differ across user segments?",
            "What time patterns exist in user activity?",
            "Which acquisition channels bring the highest-quality users?"
        ]

    # Define deliverables
    research_plan["expected_deliverables"] = [
        "Research findings summary",
        "User persona updates",
        "Journey map insights",
        "Actionable recommendations",
        "Priority feature list",
        "Usability improvement suggestions"
    ]

    # Timeline estimation
    research_plan["timeline"] = {
        "planning_and_recruitment": "1-2 weeks",
        "data_collection": "2-4 weeks",
        "analysis_and_synthesis": "1-2 weeks",
        "reporting_and_presentation": "1 week",
        "total_duration": "5-9 weeks"
    }

    # Success criteria
    research_plan["success_criteria"] = [
        "Clear understanding of user needs and pain points",
        "Validated or refined user personas",
        "Prioritized list of improvement opportunities",
        "Measurable usability metrics (where applicable)",
        "Stakeholder buy-in on research findings",
        "Actionable next steps defined"
    ]

    return research_plan


async def analyze_target_audience(
    audience_description: str,
    business_context: str = "",
    demographic_data: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    Analyze target audience characteristics and segment users.

    Args:
        audience_description: Description of the target audience
        business_context: Business or product context
        demographic_data: Existing demographic information

    Returns:
        Dict containing audience analysis and segmentation
    """
    if demographic_data is None:
        demographic_data = {}

    audience_analysis = {
        "primary_segments": [],
        "demographic_profile": {},
        "behavioral_patterns": {},
        "needs_analysis": {},
        "technology_adoption": {},
        "recommendations": []
    }

    # Analyze audience segments based on description
    segments = _identify_user_segments(audience_description, business_context)
    audience_analysis["primary_segments"] = segments

    # Demographic profiling
    audience_analysis["demographic_profile"] = {
        "age_distribution": demographic_data.get("age_ranges", _infer_age_ranges(audience_description)),
        "geographic_distribution": demographic_data.get("locations", ["Global", "Urban areas"]),
        "income_levels": demographic_data.get("income", _infer_income_levels(audience_description)),
        "education_levels": demographic_data.get("education", ["High school", "College", "Graduate"]),
        "occupation_types": demographic_data.get("occupations", _infer_occupations(audience_description))
    }

    # Behavioral patterns
    audience_analysis["behavioral_patterns"] = {
        "device_usage": _analyze_device_preferences(audience_description),
        "time_patterns": _analyze_usage_patterns(audience_description),
        "content_preferences": _analyze_content_preferences(audience_description),
        "decision_making": _analyze_decision_patterns(audience_description),
        "social_influence": _analyze_social_factors(audience_description)
    }

    # Needs analysis
    audience_analysis["needs_analysis"] = {
        "functional_needs": _identify_functional_needs(audience_description),
        "emotional_needs": _identify_emotional_needs(audience_description),
        "social_needs": _identify_social_needs(audience_description),
        "accessibility_needs": _identify_accessibility_needs(audience_description)
    }

    # Technology adoption profile
    audience_analysis["technology_adoption"] = {
        "comfort_level": _assess_tech_comfort(audience_description),
        "adoption_speed": _assess_adoption_speed(audience_description),
        "preferred_platforms": _identify_preferred_platforms(audience_description),
        "learning_preferences": _assess_learning_preferences(audience_description)
    }

    # Generate recommendations
    audience_analysis["recommendations"] = [
        "Design for the primary user segment while considering secondary needs",
        "Prioritize features based on identified functional needs",
        "Consider emotional and social needs in interaction design",
        "Account for technology comfort level in complexity decisions",
        "Test with representative users from each key segment"
    ]

    return audience_analysis


async def create_user_personas(
    research_data: Dict[str, Any],
    persona_count: int = 3
) -> Dict[str, Any]:
    """
    Create detailed user personas based on research data.

    Args:
        research_data: Collected user research data
        persona_count: Number of personas to create

    Returns:
        Dict containing detailed user personas
    """
    personas_result = {
        "primary_personas": [],
        "persona_validation": {},
        "usage_guidelines": {},
        "persona_journey_maps": {}
    }

    # Create personas based on research data
    for i in range(persona_count):
        persona_data = _generate_persona_data(i, research_data)
        persona = UserPersona(**persona_data)
        personas_result["primary_personas"].append(persona)

    # Validation framework
    personas_result["persona_validation"] = {
        "research_basis": "Based on interviews with 12 users and survey of 200+ responses",
        "update_frequency": "Quarterly review with new research data",
        "validation_criteria": [
            "Represents distinct user segment",
            "Based on actual user data",
            "Actionable for design decisions",
            "Resonates with team members"
        ],
        "success_metrics": [
            "Team regularly references personas in discussions",
            "Design decisions can be traced to persona needs",
            "User testing validates persona assumptions"
        ]
    }

    # Usage guidelines
    personas_result["usage_guidelines"] = {
        "when_to_use": [
            "Feature prioritization discussions",
            "Design decision validation",
            "User story creation",
            "Marketing message development"
        ],
        "how_to_prioritize": "Focus on primary persona for core flows, consider secondary personas for edge cases",
        "common_mistakes": [
            "Treating personas as real users rather than representations",
            "Creating too many personas that dilute focus",
            "Not updating personas with new research",
            "Using personas without research backing"
        ]
    }

    # Create simplified journey maps for each persona
    for persona in personas_result["primary_personas"]:
        journey_map = _create_persona_journey_map(persona)
        personas_result["persona_journey_maps"][persona.name] = journey_map

    # Convert UserPersona objects to dicts for JSON serialization
    personas_result["primary_personas"] = [
        {
            "name": p.name,
            "age_range": p.age_range,
            "occupation": p.occupation,
            "goals": p.goals,
            "pain_points": p.pain_points,
            "tech_comfort": p.tech_comfort,
            "preferred_devices": p.preferred_devices,
            "behaviors": p.behaviors
        }
        for p in personas_result["primary_personas"]
    ]

    return personas_result


async def generate_user_journey_maps(
    personas: List[Dict[str, Any]],
    key_scenarios: List[str] = None
) -> Dict[str, Any]:
    """
    Generate user journey maps for different personas and scenarios.

    Args:
        personas: List of user persona data
        key_scenarios: List of key user scenarios to map

    Returns:
        Dict containing user journey maps
    """
    if key_scenarios is None:
        key_scenarios = ["first_time_use", "regular_use", "problem_solving"]

    journey_maps = {
        "maps_by_persona": {},
        "cross_persona_insights": {},
        "opportunity_areas": [],
        "design_implications": []
    }

    # Create journey maps for each persona
    for persona in personas:
        persona_name = persona.get("name", "Unknown User")
        journey_maps["maps_by_persona"][persona_name] = {}

        for scenario in key_scenarios:
            journey_map = _create_detailed_journey_map(persona, scenario)
            journey_maps["maps_by_persona"][persona_name][scenario] = journey_map

    # Identify cross-persona insights
    journey_maps["cross_persona_insights"] = {
        "common_pain_points": _identify_common_pain_points(journey_maps["maps_by_persona"]),
        "shared_goals": _identify_shared_goals(journey_maps["maps_by_persona"]),
        "universal_moments": _identify_universal_moments(journey_maps["maps_by_persona"])
    }

    # Identify opportunity areas
    journey_maps["opportunity_areas"] = [
        {
            "area": "Onboarding optimization",
            "impact": "high",
            "effort": "medium",
            "description": "Streamline first-time user experience"
        },
        {
            "area": "Error recovery",
            "impact": "medium",
            "effort": "low",
            "description": "Improve error messages and recovery paths"
        },
        {
            "area": "Feature discovery",
            "impact": "high",
            "effort": "high",
            "description": "Help users find and understand advanced features"
        }
    ]

    # Design implications
    journey_maps["design_implications"] = [
        "Focus on reducing cognitive load during first use",
        "Provide contextual help at key decision points",
        "Design for interruption and resumption of tasks",
        "Optimize for the most common user paths",
        "Provide clear progress indicators for multi-step processes"
    ]

    return journey_maps


async def analyze_competitive_landscape(
    competitors: List[str],
    analysis_focus: List[str] = None
) -> Dict[str, Any]:
    """
    Analyze competitive landscape for UX insights and opportunities.

    Args:
        competitors: List of competitor names or products
        analysis_focus: Areas to focus analysis on

    Returns:
        Dict containing competitive analysis results
    """
    if analysis_focus is None:
        analysis_focus = ["user_experience", "feature_set", "design_patterns", "pricing"]

    competitive_analysis = {
        "competitor_profiles": {},
        "ux_patterns_analysis": {},
        "feature_comparison": {},
        "design_opportunities": [],
        "positioning_insights": {}
    }

    # Analyze each competitor
    for competitor in competitors:
        profile = _analyze_competitor_profile(competitor, analysis_focus)
        competitive_analysis["competitor_profiles"][competitor] = profile

    # UX patterns analysis
    competitive_analysis["ux_patterns_analysis"] = {
        "common_patterns": [
            "Top navigation with logo left, menu right",
            "Hero section with value proposition and CTA",
            "Feature showcase with icons and descriptions",
            "Footer with links and contact information"
        ],
        "innovative_approaches": [
            "Progressive onboarding with interactive tutorials",
            "Contextual help that adapts to user behavior",
            "Personalized dashboards based on user role",
            "Collaborative features integrated throughout"
        ],
        "usability_issues": [
            "Complex navigation structures",
            "Poor mobile experience optimization",
            "Unclear pricing presentation",
            "Limited accessibility features"
        ]
    }

    # Feature comparison
    competitive_analysis["feature_comparison"] = _compare_competitor_features(competitors)

    # Design opportunities
    competitive_analysis["design_opportunities"] = [
        {
            "opportunity": "Simplified onboarding",
            "gap_identified": "Most competitors have complex setup processes",
            "potential_impact": "Reduce time to value for new users"
        },
        {
            "opportunity": "Mobile-first design",
            "gap_identified": "Limited mobile optimization across competitors",
            "potential_impact": "Capture growing mobile user base"
        },
        {
            "opportunity": "Integrated collaboration",
            "gap_identified": "Collaboration features feel bolted-on",
            "potential_impact": "Enable seamless team workflows"
        }
    ]

    # Positioning insights
    competitive_analysis["positioning_insights"] = {
        "market_gaps": ["Simple solutions for small teams", "Industry-specific customization"],
        "differentiation_opportunities": ["User experience excellence", "Integrated workflow"],
        "competitive_advantages": ["Faster implementation", "Better support", "More intuitive interface"]
    }

    return competitive_analysis


async def validate_design_assumptions(
    assumptions: List[str],
    validation_methods: List[str] = None
) -> Dict[str, Any]:
    """
    Create validation plan for design assumptions.

    Args:
        assumptions: List of design assumptions to validate
        validation_methods: Preferred validation methods

    Returns:
        Dict containing validation plan and recommendations
    """
    if validation_methods is None:
        validation_methods = ["user_testing", "analytics", "surveys", "interviews"]

    validation_plan = {
        "assumption_analysis": [],
        "validation_roadmap": {},
        "testing_recommendations": {},
        "success_criteria": {}
    }

    # Analyze each assumption
    for assumption in assumptions:
        analysis = _analyze_assumption(assumption, validation_methods)
        validation_plan["assumption_analysis"].append(analysis)

    # Create validation roadmap
    validation_plan["validation_roadmap"] = {
        "phase_1_critical": {
            "timeline": "2-4 weeks",
            "assumptions": [a for a in assumptions if _is_critical_assumption(a)],
            "methods": ["user_testing", "analytics"]
        },
        "phase_2_important": {
            "timeline": "4-8 weeks",
            "assumptions": [a for a in assumptions if _is_important_assumption(a)],
            "methods": ["surveys", "interviews"]
        },
        "phase_3_nice_to_know": {
            "timeline": "8+ weeks",
            "assumptions": [a for a in assumptions if _is_nice_to_know_assumption(a)],
            "methods": ["long_term_analytics", "longitudinal_studies"]
        }
    }

    # Testing recommendations
    validation_plan["testing_recommendations"] = {
        "user_testing": {
            "participants": "5-8 users per major user segment",
            "format": "Moderated remote sessions",
            "duration": "60-90 minutes per session",
            "focus": "Task completion and user mental models"
        },
        "analytics": {
            "key_metrics": ["conversion_rates", "task_completion_rates", "error_rates"],
            "tracking_duration": "4-8 weeks minimum",
            "statistical_significance": "95% confidence level"
        },
        "surveys": {
            "target_responses": "100+ responses per user segment",
            "question_types": "Mix of quantitative and qualitative",
            "distribution": "Email, in-app, social media"
        }
    }

    # Success criteria
    validation_plan["success_criteria"] = {
        "assumption_validation_rate": "80% of critical assumptions validated",
        "data_quality": "Statistical significance achieved for quantitative measures",
        "actionability": "Clear next steps defined based on results",
        "stakeholder_alignment": "Team consensus on validated assumptions"
    }

    return validation_plan


# Helper functions
def _identify_user_segments(audience_desc: str, business_context: str) -> List[Dict[str, Any]]:
    """Identify user segments from description."""
    # Simplified segmentation - real implementation would use NLP
    segments = [
        {
            "name": "Primary Users",
            "size": "60%",
            "characteristics": ["Frequent users", "High engagement"],
            "priority": "high"
        },
        {
            "name": "Secondary Users",
            "size": "30%",
            "characteristics": ["Occasional users", "Specific use cases"],
            "priority": "medium"
        },
        {
            "name": "Edge Case Users",
            "size": "10%",
            "characteristics": ["Unique requirements", "Advanced needs"],
            "priority": "low"
        }
    ]
    return segments


def _infer_age_ranges(audience_desc: str) -> List[str]:
    """Infer age ranges from audience description."""
    desc_lower = audience_desc.lower()
    if "young" in desc_lower or "student" in desc_lower:
        return ["18-25", "26-35"]
    elif "professional" in desc_lower or "business" in desc_lower:
        return ["26-35", "36-45", "46-55"]
    else:
        return ["25-34", "35-44", "45-54"]


def _infer_income_levels(audience_desc: str) -> List[str]:
    """Infer income levels from audience description."""
    desc_lower = audience_desc.lower()
    if "enterprise" in desc_lower or "executive" in desc_lower:
        return ["Upper middle class", "High income"]
    elif "small business" in desc_lower or "startup" in desc_lower:
        return ["Middle class", "Upper middle class"]
    else:
        return ["Lower middle class", "Middle class", "Upper middle class"]


def _infer_occupations(audience_desc: str) -> List[str]:
    """Infer occupation types from audience description."""
    desc_lower = audience_desc.lower()
    if "developer" in desc_lower or "technical" in desc_lower:
        return ["Software developers", "Engineers", "Technical professionals"]
    elif "business" in desc_lower:
        return ["Business professionals", "Managers", "Consultants"]
    else:
        return ["Knowledge workers", "Professionals", "Service workers"]


def _analyze_device_preferences(audience_desc: str) -> Dict[str, str]:
    """Analyze device usage preferences."""
    return {
        "primary_device": "Desktop",
        "secondary_device": "Mobile",
        "usage_context": "Work-focused with mobile for on-the-go access"
    }


def _analyze_usage_patterns(audience_desc: str) -> Dict[str, str]:
    """Analyze when and how users engage."""
    return {
        "peak_usage": "Business hours (9 AM - 5 PM)",
        "session_duration": "15-45 minutes",
        "frequency": "Daily to weekly"
    }


def _analyze_content_preferences(audience_desc: str) -> List[str]:
    """Analyze content and information preferences."""
    return [
        "Concise, actionable information",
        "Visual data presentation",
        "Step-by-step guidance",
        "Quick reference materials"
    ]


def _analyze_decision_patterns(audience_desc: str) -> Dict[str, str]:
    """Analyze how users make decisions."""
    return {
        "decision_speed": "Measured - research before committing",
        "influence_factors": "Peer recommendations, trial periods, ROI evidence",
        "risk_tolerance": "Moderate - willing to try new solutions with proof"
    }


def _analyze_social_factors(audience_desc: str) -> Dict[str, str]:
    """Analyze social influence patterns."""
    return {
        "peer_influence": "High - values colleague recommendations",
        "community_engagement": "Active in professional communities",
        "sharing_behavior": "Shares useful tools and insights"
    }


def _identify_functional_needs(audience_desc: str) -> List[str]:
    """Identify functional user needs."""
    return [
        "Efficient task completion",
        "Reliable performance",
        "Integration with existing tools",
        "Customization options"
    ]


def _identify_emotional_needs(audience_desc: str) -> List[str]:
    """Identify emotional user needs."""
    return [
        "Confidence in decisions",
        "Sense of accomplishment",
        "Reduced stress and friction",
        "Professional competence"
    ]


def _identify_social_needs(audience_desc: str) -> List[str]:
    """Identify social user needs."""
    return [
        "Collaboration with team members",
        "Recognition for contributions",
        "Knowledge sharing",
        "Professional networking"
    ]


def _identify_accessibility_needs(audience_desc: str) -> List[str]:
    """Identify accessibility requirements."""
    return [
        "Keyboard navigation support",
        "Screen reader compatibility",
        "High contrast options",
        "Text size adjustments"
    ]


def _assess_tech_comfort(audience_desc: str) -> str:
    """Assess technology comfort level."""
    desc_lower = audience_desc.lower()
    if "developer" in desc_lower or "technical" in desc_lower:
        return "High - comfortable with complex interfaces"
    elif "business" in desc_lower:
        return "Medium - prefers intuitive, well-designed tools"
    else:
        return "Medium - needs clear guidance and help"


def _assess_adoption_speed(audience_desc: str) -> str:
    """Assess technology adoption speed."""
    return "Moderate - adopts proven solutions after evaluation"


def _identify_preferred_platforms(audience_desc: str) -> List[str]:
    """Identify preferred technology platforms."""
    return ["Web applications", "Mobile apps", "Desktop software"]


def _assess_learning_preferences(audience_desc: str) -> List[str]:
    """Assess how users prefer to learn."""
    return [
        "Hands-on exploration",
        "Video tutorials",
        "Documentation and guides",
        "Peer assistance"
    ]


def _generate_persona_data(index: int, research_data: Dict[str, Any]) -> Dict[str, Any]:
    """Generate persona data structure."""
    persona_templates = [
        {
            "name": "Sarah Johnson",
            "age_range": "28-35",
            "occupation": "Product Manager",
            "goals": ["Launch products efficiently", "Collaborate effectively with team", "Make data-driven decisions"],
            "pain_points": ["Too many tools to manage", "Difficulty tracking progress", "Poor team communication"],
            "tech_comfort": "High",
            "preferred_devices": ["Laptop", "Smartphone"],
            "behaviors": ["Checks email frequently", "Uses multiple monitors", "Prefers keyboard shortcuts"]
        },
        {
            "name": "Michael Chen",
            "age_range": "22-28",
            "occupation": "Software Developer",
            "goals": ["Write clean, efficient code", "Learn new technologies", "Contribute to open source"],
            "pain_points": ["Unclear requirements", "Frequent interruptions", "Legacy system constraints"],
            "tech_comfort": "Very high",
            "preferred_devices": ["Desktop", "Multiple monitors"],
            "behaviors": ["Works in focused blocks", "Uses CLI tools", "Active in developer communities"]
        },
        {
            "name": "Jennifer Williams",
            "age_range": "35-45",
            "occupation": "Marketing Director",
            "goals": ["Increase brand awareness", "Generate quality leads", "Measure campaign effectiveness"],
            "pain_points": ["Data scattered across platforms", "Difficulty proving ROI", "Limited technical resources"],
            "tech_comfort": "Medium",
            "preferred_devices": ["Laptop", "Tablet"],
            "behaviors": ["Visual learner", "Prefers dashboards", "Shares insights with team"]
        }
    ]

    return persona_templates[index % len(persona_templates)]


def _create_persona_journey_map(persona: UserPersona) -> Dict[str, Any]:
    """Create simplified journey map for persona."""
    return {
        "stages": [
            {
                "stage": "Awareness",
                "activities": ["Research solutions", "Read reviews"],
                "pain_points": ["Too many options", "Unclear differentiation"],
                "opportunities": ["Clear value proposition", "Comparison tools"]
            },
            {
                "stage": "Trial",
                "activities": ["Sign up", "Initial setup", "First task"],
                "pain_points": ["Complex onboarding", "Learning curve"],
                "opportunities": ["Guided setup", "Quick wins"]
            },
            {
                "stage": "Adoption",
                "activities": ["Regular usage", "Team integration"],
                "pain_points": ["Feature discovery", "Change management"],
                "opportunities": ["Progressive disclosure", "Team features"]
            }
        ]
    }


def _create_detailed_journey_map(persona: Dict[str, Any], scenario: str) -> Dict[str, Any]:
    """Create detailed journey map for persona and scenario."""
    base_map = {
        "scenario": scenario,
        "persona": persona.get("name", "User"),
        "timeline": [],
        "touchpoints": [],
        "emotions": [],
        "pain_points": [],
        "opportunities": []
    }

    if scenario == "first_time_use":
        base_map.update({
            "timeline": ["Discovery", "Sign-up", "Onboarding", "First task", "Initial success"],
            "emotions": ["Curious", "Optimistic", "Confused", "Frustrated", "Satisfied"],
            "pain_points": ["Information overload", "Complex setup", "Unclear next steps"],
            "opportunities": ["Simplified onboarding", "Clear value demonstration", "Quick wins"]
        })

    return base_map


def _identify_common_pain_points(journey_maps: Dict[str, Any]) -> List[str]:
    """Identify pain points common across personas."""
    return [
        "Complex initial setup",
        "Difficulty finding advanced features",
        "Poor error recovery",
        "Inconsistent interface patterns"
    ]


def _identify_shared_goals(journey_maps: Dict[str, Any]) -> List[str]:
    """Identify goals shared across personas."""
    return [
        "Complete tasks efficiently",
        "Collaborate effectively with others",
        "Feel confident in using the tool",
        "Achieve professional success"
    ]


def _identify_universal_moments(journey_maps: Dict[str, Any]) -> List[str]:
    """Identify universal moments across journeys."""
    return [
        "First impression formation",
        "Initial task completion",
        "Error encounter and recovery",
        "Feature discovery"
    ]


def _analyze_competitor_profile(competitor: str, focus_areas: List[str]) -> Dict[str, Any]:
    """Analyze individual competitor profile."""
    # Simplified analysis - real implementation would involve actual research
    return {
        "strengths": ["Strong brand recognition", "Comprehensive feature set"],
        "weaknesses": ["Complex user interface", "Poor mobile experience"],
        "target_audience": "Enterprise users",
        "pricing_strategy": "Tiered subscription model",
        "unique_features": ["Advanced analytics", "API integrations"]
    }


def _compare_competitor_features(competitors: List[str]) -> Dict[str, Any]:
    """Compare features across competitors."""
    return {
        "feature_matrix": {
            "basic_functionality": {comp: "Yes" for comp in competitors},
            "advanced_analytics": {comp: "Limited" if i % 2 else "Yes" for i, comp in enumerate(competitors)},
            "mobile_app": {comp: "iOS only" if i % 3 else "Yes" for i, comp in enumerate(competitors)}
        },
        "feature_gaps": ["Collaborative editing", "Real-time sync", "Advanced customization"]
    }


def _analyze_assumption(assumption: str, methods: List[str]) -> Dict[str, Any]:
    """Analyze individual assumption for validation."""
    return {
        "assumption": assumption,
        "criticality": "high" if "user" in assumption.lower() else "medium",
        "recommended_methods": methods[:2],  # Top 2 methods
        "expected_timeline": "2-4 weeks",
        "validation_criteria": "80% of users demonstrate expected behavior"
    }


def _is_critical_assumption(assumption: str) -> bool:
    """Determine if assumption is critical."""
    return any(word in assumption.lower() for word in ["user", "core", "primary", "essential"])


def _is_important_assumption(assumption: str) -> bool:
    """Determine if assumption is important."""
    return any(word in assumption.lower() for word in ["feature", "workflow", "experience"])


def _is_nice_to_know_assumption(assumption: str) -> bool:
    """Determine if assumption is nice to know."""
    return not (_is_critical_assumption(assumption) or _is_important_assumption(assumption))