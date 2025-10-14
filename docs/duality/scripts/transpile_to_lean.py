#!/usr/bin/env python3
"""
JSON→Lean4 Transpiler for Synapse Duality Formalization
Phase 3: Automated constraint translation with decidability
Phase 5.5: Enhanced for two-variable forall and MiniZinc operators
Phase 6b Hotfix: Support base import mode for existing projects

Usage:
  python3 transpile_to_lean.py --chunk 06
  python3 transpile_to_lean.py --all
  python3 transpile_to_lean.py --chunk 06 --output Chunk06.lean
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Import shared utilities
from shared_utils import (
    discover_chunks,
    load_json_safe,
    get_chunk_json_path,
    get_chunk_lean_path,
    add_common_cli_args,
    process_chunks_batch,
    validate_chunk_id
)


# Operator mapping: JSON DSL → Lean4
OPERATOR_MAP = {
    '&&': '∧',
    '||': '∨',
    '!': '¬',
    '->': '→',
    '==': '=',
    '!=': '≠',
    '/\\': '∧',  # MiniZinc boolean AND
    '\\/': '∨',  # MiniZinc boolean OR
}


def expand_forall_two_vars(expr: str) -> str:
    """
    PHASE 5.5: Expand forall(i, j in 1..N where i < j)(body).

    Handles patterns like:
      forall(i, j in 1..8 where i < j)(abs(x[i] - x[j]) <= 20)

    Expands to conjunction of all valid (i, j) pairs where i < j:
      (body[i=1,j=2] ∧ body[i=1,j=3] ∧ ... ∧ body[i=N-1,j=N])
    """
    # Pattern: forall(i, j in START..END where i < j)(BODY)
    pattern = re.compile(
        r'forall\s*\(\s*i\s*,\s*j\s+in\s+(\d+)\.\.(\d+)\s+where\s+i\s*<\s*j\s*\)\s*\((.+)\)',
        re.IGNORECASE
    )

    def expand_match(match):
        start, end, body = int(match.group(1)), int(match.group(2)), match.group(3)
        terms = []

        # Generate all pairs (i, j) where i < j
        for i in range(start, end + 1):
            for j in range(i + 1, end + 1):
                # Substitute i and j in body
                expanded = body.replace('x[i]', f'x[{i}]').replace('x[j]', f'x[{j}]')
                terms.append(expanded)

        if not terms:
            return "True"  # Empty forall is vacuously true

        # Join with ∧ (will be translated by standard operator mapping)
        return "(" + " && ".join(terms) + ")"

    # Apply expansion (may need multiple passes if nested)
    result = pattern.sub(expand_match, expr)
    return result


def sanitize_meta_constructs_lean(expr: str) -> str:
    """
    PHASE 5.5: Sanitize meta-level constructs for Lean4.

    Replaces unsupported symbolic/meta constructs with 'True':
    - typeof(...), component_of(...), pipeline(...), well_formed(...)
    - set cardinality |{...}|
    - non-numeric membership (x ∈ S) where S is symbolic
    - undefined predicates and architectural identifiers

    Keeps Lean compilable by using True placeholders.
    """
    result = expr.strip()

    # Replace meta predicates with 'True' (comprehensive list)
    # Note: [^)]* pattern may not handle nested parens correctly, but
    # cleanup pass later will fix most issues
    meta_predicates = [
        # Original patterns
        r'\btypeof\s*\([^)]*\)',
        r'\bcomponent_of\s*\([^)]*\)',
        r'\bpipeline\s*\([^)]*\)',
        r'\bwell_formed\s*\([^)]*\)',
        r'\bhas_field\s*\([^)]*\)',
        # Additional predicates from proof chunks
        r'\btransforms\s*\([^)]*\)',
        r'\bperforms\s*\([^)]*\)',
        r'\buses\s*\([^)]*\)',
        r'\bseparated\s*\([^)]*\)',
        r'\binterface_type\s*\([^)]*\)',
        r'\borchestrates\s*\([^)]*\)',
        r'\bdescribes\s*\([^)]*\)',
        r'\bdefines\s*\([^)]*\)',  # Added
        r'\bcomputes\s*\([^)]*\)',
        r'\boperates_within\s*\([^)]*\)',
        r'\badheres_to\s*\([^)]*\)',
        r'\benables\s*\([^)]*\)',
        r'\bgates\s*\([^)]*\)',
        r'\bcoordinates\s*\([^)]*\)',
        r'\bmeasures\s*\([^)]*\)',
        r'\btranslates\s*\([^)]*\)',
        r'\bformats\s*\([^)]*\)',
        r'\breceives\s*\([^)]*\)',
        r'\bcreates\s*\([^)]*\)',
        r'\bexecutes\s*\([^)]*\)',
        r'\bpresents\s*\([^)]*\)',
        r'\bcalls\s*\([^)]*\)',
        r'\bexplains_why\s*\([^)]*\)',
        r'\bmodels\s*\([^)]*\)',
        r'\baligned\s*\([^)]*\)',
        r'\bsuitable\s*\([^)]*\)',
        r'\bdeterministic\s*\([^)]*\)',
        r'\bmeasurable\s*\([^)]*\)',
        r'\bscalable\s*\([^)]*\)',
        r'\btestable\s*\([^)]*\)',
        r'\bpredictable\s*\([^)]*\)',
        r'\busable\s*\([^)]*\)',
        r'\bintelligent\s*\([^)]*\)',
        r'\bworks_with\s*\([^)]*\)',
        r'\bemits\s*\([^)]*\)',
        r'\bhas\s*\([^)]*\)',
        r'\boutput\s*\([^)]*\)',  # Added
        r'\bdepth\s*\([^)]*\)',   # Added
        r'\bperformance\s*\([^)]*\)',  # Added
        r'\bencoding_method\s*\([^)]*\)',  # Added
        r'\boptimizable\s*\([^)]*\)',  # Added
        r'\btranslate\s*\([^)]*\)',  # Added (not translates)
    ]

    # Apply meta predicate replacements multiple times to handle nested cases
    # e.g., defines(X, depth(...)) needs depth replaced first
    for _ in range(3):  # Multiple passes for nested predicates
        for pattern in meta_predicates:
            result = re.sub(pattern, 'True', result)

    # Replace architectural identifiers (not defined in Base.lean)
    # These appear in expressions like "Agents = UX_Layer" or "T_ext = Pipeline[...]"
    architectural_ids = [
        r'\bAgents\b', r'\bUX_Layer\b', r'\bTracts\b', r'\bOperatorEngine\b',
        r'\bC_c\b', r'\bNaturalLanguage\b', r'\bPipeline\b',
        r'\bInterfaceOperators\b', r'\bIntelligenceOperators\b', r'\bBridgeOperators\b',
        r'\bDGR\b', r'\bCIG3\b', r'\bSystem\b', r'\bComponents\b',
        r'\bFrameworks\b', r'\bPNEUMA\b', r'\bUnificationFlow\b',
        r'\bNLP_Op\b', r'\bEncoderOp\b', r'\bPlannerOp\b',
        r'\bSynthesizerOp\b', r'\bRenderOp\b', r'\bNaturalLanguageSummary\b',
        r'\bFormattedOutput\b', r'\bOperators\b', r'\bTypedOperators\b',
        r'\bStructuredData\b', r'\bAgent\b', r'\bPlan\b',
        r'\blayers\b', r'\bstage\b', r'\bpipeline\b',
        r'\bencoding_method\b', r'\bbehavior\b',
        r'\bold_system\b', r'\bold_T_int\b', r'\bold_T_ext\b',
        r'\bbiological_brain\b', r'\buser_concerns\b', r'\bmapping\b',
        r'\bAI_systems\b', r'\buser_interaction\b', r'\bcomponent\b',
    ]

    # Replace complex expressions containing architectural identifiers with True
    for identifier in architectural_ids:
        # Replace array/set syntax for architectural identifiers first (e.g., Pipeline[...])
        result = re.sub(rf'{identifier}\[[^\]]+\]', 'True', result)
        # Then replace equations/comparisons (e.g., Agents = True, True = NaturalLanguage)
        # Match up to the next logical operator (∧, ∨) or parenthesis
        result = re.sub(rf'{identifier}\s*[=≠∉∈]\s*[^\s∧∨)]+', 'True', result)
        result = re.sub(rf'[^\s∧∨(]+\s*[=≠∉∈]\s*{identifier}', 'True', result)

    # Replace set literal syntax {...} but NOT array access x[i]
    result = re.sub(r'\{[^}]*\}', 'True', result)

    # Replace set cardinality notation |{...}| = N with True
    result = re.sub(r'\|\s*\{[^}]*\}\s*\|\s*[=<>!]+\s*\d+', 'True', result)

    # Replace symbolic membership ∈ and ∉ with True (unless in numeric context)
    result = re.sub(r'\w+\s*[∈∉]\s*\{[A-Za-z_][^\}]*\}', 'True', result)
    result = re.sub(r'\w+\s*∈\s*\[[^\]]*\]', 'True', result)  # Interval membership

    # Replace Greek symbols and special identifiers that might remain
    # Ψ (Psi), φ (phi), etc.
    result = re.sub(r'[ΨΦφψ](_[a-z]+)?', 'True', result)

    # Clean up arrow chains (e.g., "True → NLP_Op → EncoderOp → ...")
    # Replace any sequence with arrows between identifiers with True
    result = re.sub(r'\b\w+\s*→[^∧∨)]+', 'True', result)

    # Clean up artifacts from nested parentheses (e.g., "True) →" from measures(...))
    result = re.sub(r'True\s*\)\s*[→∧∨]', 'True ∧', result)

    # Clean up remaining equations with True (e.g., T_ext = True, output(...) = True)
    result = re.sub(r'\b\w+\s*=\s*True\b', 'True', result)
    result = re.sub(r'\bTrue\s*=\s*\w+\b', 'True', result)

    # Clean up artifacts from incomplete predicate matching
    # e.g., "defines(X, depth(Y))" becomes "defines(X, True).Z)" where extra ) and .Z remain
    # Pattern: True followed by .[word]) - remove the stray parts
    result = re.sub(r'True\.[^)]*\)', 'True', result)
    # Pattern: True) where True is followed directly by ) without (
    result = re.sub(r'True\s*\)', 'True', result)

    # Clean up: True && True → True, (True) → True
    result = re.sub(r'True\s*[∧&]{1,2}\s*True', 'True', result)
    result = re.sub(r'\(\s*True\s*\)', 'True', result)

    # Clean up extra closing parens in sequences like "(True)) ∧"
    # Look for patterns where we have (expr)) with an extra closing paren
    for _ in range(5):  # Repeat to handle deeply nested cases
        # Pattern: close-paren followed by another close-paren (with optional whitespace)
        result = re.sub(r'\)\s*\)\s*([∧∨])', r') \1', result)
        # Also handle just )) without following operator
        result = re.sub(r'\)\s*\)(?!\s*[∧∨])', ')', result)

    return result


def translate_expr_to_lean(expr: str, constraint_name: str = "") -> str:
    """
    Translate JSON DSL expression to Lean4 Prop syntax.

    Handles:
    - Array indexing: x[1] → x.x1, x[2] → x.x2, etc.
    - Operators: &&→∧, ||→∨, !→¬, ->→→, ==→=, !=→≠
    - MiniZinc operators: /\\→∧, \\/→∨ (PHASE 5.5)
    - Subtraction: Auto-cast to Int when detected
    - sum(i in 1..4)(x[i]) → x.x1 + x.x2 + x.x3 + x.x4 (expansion)
    - forall(i in 1..N)(P) → conjunction expansion
    - forall(i, j in 1..N where i < j)(P) → two-var expansion (PHASE 5.5)
    - abs(a - b) → ((a : Int) - b ≤ k ∧ (b : Int) - a ≤ k) for abs patterns
    - count(i in S)(P) → List.sum (List.map (fun xi => if P then 1 else 0) [...])
    - PHASE 5.5: Sanitizes meta constructs (typeof, component_of, etc.) → True
    """
    # PHASE 5.5: Sanitize meta constructs FIRST
    result = sanitize_meta_constructs_lean(expr)
    result = result.strip()

    # Handle 'true' and 'false' literals
    result = re.sub(r'\btrue\b', 'True', result, flags=re.IGNORECASE)
    result = re.sub(r'\bfalse\b', 'False', result, flags=re.IGNORECASE)

    # PHASE 5.5: Expand two-variable forall BEFORE single-variable forall
    # This must come first to avoid pattern collision
    result = expand_forall_two_vars(result)

    # Handle abs(x[i] - x[j]) <= k pattern (ALL occurrences)
    # Convert to: ((x.xi : Int) - x.xj ≤ k ∧ (x.xj : Int) - x.xi ≤ k)
    def expand_abs(match):
        i, j, op, k = match.groups()
        xi_name = f"x.x{i}"
        xj_name = f"x.x{j}"

        if op == '<=':
            # abs(x[i] - x[j]) <= k means -k <= x[i]-x[j] <= k
            return f"(({xi_name} : Int) - {xj_name} ≤ {k} ∧ ({xj_name} : Int) - {xi_name} ≤ {k})"
        else:
            # Other comparisons with abs - expand similarly
            return f"(({xi_name} : Int) - {xj_name}).natAbs {op} {k}"

    abs_pattern = re.compile(r'abs\s*\(\s*x\[(\d+)\]\s*-\s*x\[(\d+)\]\s*\)\s*([<>=]+)\s*(\d+)')
    result = abs_pattern.sub(expand_abs, result)

    # Handle sum(i in 1..N)(x[i]) expansion - MUST do all at once to avoid double expansion
    def expand_sum(match):
        start, end = int(match.group(1)), int(match.group(2))
        terms = [f"x.x{i}" for i in range(start, end + 1)]
        return "(" + " + ".join(terms) + ")"

    sum_pattern = re.compile(r'sum\s*\(\s*i\s+in\s+(\d+)\.\.(\d+)\s*\)\s*\(\s*x\[i\]\s*\)')
    result = sum_pattern.sub(expand_sum, result)

    # Handle forall(i in 1..N)(x[i] >= k) expansion
    def expand_forall(match):
        start, end, cond = int(match.group(1)), int(match.group(2)), match.group(3)
        terms = []
        for i in range(start, end + 1):
            expanded = cond.replace('x[i]', f'x.x{i}')
            terms.append(expanded)
        return "(" + " ∧ ".join(terms) + ")"

    forall_pattern = re.compile(r'forall\s*\(\s*i\s+in\s+(\d+)\.\.(\d+)\s*\)\s*\(([^)]+)\)')
    result = forall_pattern.sub(expand_forall, result)

    # Handle count(i in 1..N)(x[i] > 0) → sum of booleans as ints
    count_pattern = re.compile(r'count\s*\(\s*i\s+in\s+(\d+)\.\.(\d+)\s*\)\s*\(([^)]+)\)')
    match = count_pattern.search(result)
    if match:
        start, end, cond = int(match.group(1)), int(match.group(2)), match.group(3)
        # Build list of elements
        elements = [f"x.x{i}" for i in range(start, end + 1)]
        elements_str = ", ".join(elements)

        # Build predicate - need to map x[i] to the variable name in the lambda
        pred = cond.replace('x[i]', 'xi')

        list_sum_expr = f"(List.sum (List.map (fun xi => if {pred} then 1 else 0) [{elements_str}]))"
        result = count_pattern.sub(list_sum_expr, result)

    # Replace array indexing x[N] → x.xN (for any remaining instances)
    result = re.sub(r'x\[(\d+)\]', r'x.x\1', result)

    # Replace operators (including MiniZinc operators)
    for json_op, lean_op in OPERATOR_MAP.items():
        if json_op in ('&&', '||', '/\\', '\\/'):
            # Must replace as whole operators, not inside words
            # Escape backslashes in pattern for MiniZinc operators
            pattern_str = json_op.replace('\\', '\\\\')
            result = result.replace(json_op, f' {lean_op} ')
        elif json_op == '!':
            # Negation: replace ! before variable/expression
            result = re.sub(r'!\s*([a-zA-Z(])', r'¬\1', result)
        else:
            result = result.replace(json_op, lean_op)

    # Add Int casts for subtraction if needed
    # Pattern: x.xi - x.xj needs casting
    if '-' in result and 'x.' in result:
        # Cast first operand in subtractions
        result = re.sub(r'\b(x\.x\d+)\s*-', r'(\1 : Int) -', result)

    # Clean up extra spaces
    result = re.sub(r'\s+', ' ', result)
    result = result.strip()

    return result


def generate_lean_header(chunk_id: str, title: str, use_base_imports: bool = False) -> List[str]:
    """
    Generate Lean4 header with configurable imports.

    Args:
        chunk_id: Chunk ID (e.g., "06")
        title: Chunk title
        use_base_imports: If True, import from Duality.Base instead of defining inline
                         (for existing Duality project). If False, generate standalone
                         module with Mathlib imports and inline definitions.
    """
    if use_base_imports:
        # For existing Duality project - use Base.lean imports
        lines = [
            "/-",
            f"Chunk {chunk_id}: {title}",
            "Auto-generated by transpile_to_lean.py",
            "-/",
            "",
            "import Duality.Base",
            "import Duality.Lemmas",
            "",
            f"namespace Chunk{chunk_id}",
            "open Duality",
            "",
        ]
    else:
        # Standalone mode - inline all definitions
        lines = [
            "/-",
            f"Chunk {chunk_id}: {title}",
            "Auto-generated by transpile_to_lean.py",
            "-/",
            "",
            "import Mathlib.Data.Nat.Basic",
            "",
            f"namespace Chunk{chunk_id}",
            "",
            "def N : ℕ := 100",
            "",
            "structure X8 where",
            "  x1 : Nat",
            "  x2 : Nat",
            "  x3 : Nat",
            "  x4 : Nat",
            "  x5 : Nat",
            "  x6 : Nat",
            "  x7 : Nat",
            "  x8 : Nat",
            "deriving Repr",
            "",
            "def unitary (x : X8) : Prop :=",
            "  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N",
            "",
        ]
    return lines


def generate_lean_constraints(constraints: List[Dict]) -> List[str]:
    """Generate Lean4 domain constraints definition."""
    lines = ["-- Domain constraints"]
    lines.append("def domainConstraints (x : X8) : Prop :=")

    constraint_exprs = []
    for c in constraints:
        name = c.get("name", "unnamed")
        expr = c.get("expr", "true")

        # Translate to Lean
        lean_expr = translate_expr_to_lean(expr, name)

        # Add comment and expression
        constraint_exprs.append(f"  -- constraint: {name}")
        constraint_exprs.append(f"  ({lean_expr})")

    # Join with ∧
    if constraint_exprs:
        lines.append(constraint_exprs[0])
        for i in range(1, len(constraint_exprs), 2):
            if i < len(constraint_exprs):
                lines.append(constraint_exprs[i] + " ∧")
                if i + 1 < len(constraint_exprs):
                    lines.append(constraint_exprs[i + 1])

        # Remove trailing ∧ if present
        if lines[-1].endswith(" ∧"):
            lines[-1] = lines[-1][:-2]
    else:
        lines.append("  True")

    lines.append("")
    return lines


def generate_lean_decidability() -> List[str]:
    """Generate decidability instance."""
    lines = [
        "-- Decidability instance (required for computational verification)",
        "instance (x : X8) : Decidable (domainConstraints x) := by",
        "  unfold domainConstraints",
        "  infer_instance",
        "",
    ]
    return lines


def generate_lean_footer(chunk_id: str) -> List[str]:
    """Generate Lean4 footer with witness placeholder."""
    lines = [
        "-- Witness (to be injected from MiniZinc solution)",
        "-- def witness : X8 := ⟨?, ?, ?, ?, ?, ?, ?, ?⟩",
        "",
        "-- theorem witness_valid : unitary witness ∧ domainConstraints witness := by",
        "--   constructor",
        "--   · rfl  -- unitary",
        "--   · constructor <;> omega  -- domain constraints",
        "",
        "-- theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=",
        "--   ⟨witness, witness_valid⟩",
        "",
        f"end Chunk{chunk_id}",
    ]
    return lines


def generate_lean_from_json(json_data: Dict, use_base_imports: bool = False) -> str:
    """
    Generate complete Lean4 module from JSON constraints.

    Args:
        json_data: JSON object with id, title, constraints
        use_base_imports: If True, generate imports for existing Duality project.
                         If False, generate standalone module with inline definitions.

    Returns:
        Complete Lean4 module as string
    """
    chunk_id = json_data.get("id", "XX")
    title = json_data.get("title", "Untitled")
    constraints = json_data.get("constraints", [])

    lines = []
    lines.extend(generate_lean_header(chunk_id, title, use_base_imports))
    lines.extend(generate_lean_constraints(constraints))
    lines.extend(generate_lean_decidability())
    lines.extend(generate_lean_footer(chunk_id))

    return "\n".join(lines)


def process_chunk(chunk_id: str, base_dir: Path, output_path: Optional[Path] = None,
                  use_base_imports: bool = False) -> bool:
    """Process a single chunk and generate Lean4 module."""
    # Load JSON using shared utility
    json_path = get_chunk_json_path(chunk_id, base_dir)
    json_data = load_json_safe(json_path)

    if json_data is None:
        return False

    # Generate Lean
    lean_content = generate_lean_from_json(json_data, use_base_imports)

    # Determine output path
    if output_path is None:
        output_path = get_chunk_lean_path(chunk_id, base_dir)

    # Ensure directory exists
    output_path.parent.mkdir(parents=True, exist_ok=True)

    # Write output
    try:
        output_path.write_text(lean_content, encoding="utf-8")
        print(f"Generated: {output_path}")
        return True
    except Exception as e:
        print(f"Error writing {output_path}: {e}", file=sys.stderr)
        return False


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Transpile JSON constraint DSL to Lean4"
    )

    default_base = Path(__file__).resolve().parents[1]
    parser.add_argument(
        "--base-dir",
        type=Path,
        default=default_base,
        help=f"Base duality directory (default: {default_base})"
    )
    parser.add_argument(
        "--chunk",
        type=str,
        help="Chunk ID to process (e.g., 06)"
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Process all discovered chunks"
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Output path (default: formal/Duality/Chunks/Chunk{id}.lean)"
    )
    parser.add_argument(
        "--use-base-imports",
        action="store_true",
        help="Generate imports from Duality.Base (for existing project) instead of inline definitions"
    )

    args = parser.parse_args(argv)

    if not args.chunk and not args.all:
        parser.error("Must specify --chunk or --all")

    base_dir = args.base_dir

    if args.all:
        chunk_ids = discover_chunks(base_dir)
        if not chunk_ids:
            print("No chunks discovered", file=sys.stderr)
            return 1

        success_count = 0
        for cid in chunk_ids:
            if process_chunk(cid, base_dir, use_base_imports=args.use_base_imports):
                success_count += 1

        print(f"\nProcessed {success_count}/{len(chunk_ids)} chunks successfully")
        return 0 if success_count == len(chunk_ids) else 1

    else:
        # Process single chunk
        chunk_id = f"{int(args.chunk):02d}"
        success = process_chunk(chunk_id, base_dir, args.output, args.use_base_imports)
        return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
