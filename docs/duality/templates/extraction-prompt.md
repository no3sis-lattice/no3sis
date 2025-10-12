# LLM Extraction Prompt Template

**Purpose**: Extract formal constraints from TRUE_DUAL_TRACT chunks (no reasoning/logic)

**Role**: You are a constraint extraction specialist. Your job is to identify formal invariants, bounds, and relationships from technical text and output them as structured JSON.

---

## Instructions

**Task**: Read the provided text excerpt and extract all formal constraints as JSON.

**What to Extract**:
- Mathematical invariants (e.g., "sum(x) = N", "Ψ ≥ 0.75")
- Bounds and ranges (e.g., "R_i ∈ [0,1]", "timeout ≤ 60s")
- Structural relationships (e.g., "T_ext calls C_c", "Layer L5 depends on L1-L4")
- Type constraints (e.g., "GoalSpec has fields: domain, target_Ψ")
- Cardinality constraints (e.g., "exactly 3 operators", "8D coordinates")

**What NOT to Extract**:
- Examples or scenarios (unless they define a constraint)
- Implementation details (code snippets)
- Explanatory prose
- Motivation or rationale

**Output Format**: Valid JSON matching `chunk-constraints.schema.json`

---

## Schema Reference

```json
{
  "id": "NN",
  "title": "Chunk Title",
  "goalType": "proof | search | refinement",
  "parameters": {
    "eightDimManifold": true,
    "scaleN": 100,
    "monsterPrimes": [2,3,5,7,11,13,17,19],
    "similarityObjective": "none | neighbor_distance_min | projection_fit_min",
    "godelization": { "encode": false, "base": 10 }
  },
  "constraints": [
    {
      "name": "constraint_identifier",
      "expr": "mathematical expression or logical statement",
      "notes": "optional clarification"
    }
  ]
}
```

---

## Constraint Expression Language (DSL)

**Arithmetic**:
- `sum(x[1..8]) = N` (unit-sum on 8D coords)
- `x[i] >= 0`, `x[i] <= N`

**Logical**:
- `True`, `False`
- `A ∧ B`, `A ∨ B`, `¬A`
- `A → B` (implication)
- `∀ x : P(x)`, `∃ x : P(x)`

**Relations**:
- `Ψ >= 0.75`, `R_i in [0,1]`
- `|S| = 3` (cardinality)
- `A ⊆ B` (subset)

**Structural**:
- `depends_on(L5, [L1,L2,L3,L4])`
- `calls(T_ext, C_c)`
- `has_field(GoalSpec, "domain")`

**Typing**:
- `typeof(Ψ) = Real`
- `typeof(x) = Array[1..8, Nat]`

**Keep it simple**: If unsure, use natural language in `expr` and add `notes` to clarify intent.

---

## Example Extraction

**Input Text**:
```
The External Tract (T_ext) must call the Corpus Callosum (C_c) with a valid GoalSpec.
A GoalSpec has three required fields: domain (string), target_Ψ (float ∈ [0,1]), and
context (optional dict). The system must achieve Ψ ≥ target_Ψ or fail gracefully.
```

**Output JSON**:
```json
{
  "id": "06",
  "title": "External Tract: Interface Operator Pipeline",
  "goalType": "proof",
  "parameters": {
    "eightDimManifold": true,
    "scaleN": 100,
    "monsterPrimes": [2,3,5,7,11,13,17,19],
    "similarityObjective": "none"
  },
  "constraints": [
    {
      "name": "t_ext_calls_c_c",
      "expr": "calls(T_ext, C_c)",
      "notes": "External tract must invoke Corpus Callosum"
    },
    {
      "name": "goalspec_has_domain",
      "expr": "has_field(GoalSpec, 'domain')",
      "notes": "Required field: domain (string)"
    },
    {
      "name": "goalspec_has_target_psi",
      "expr": "has_field(GoalSpec, 'target_Ψ') ∧ typeof(target_Ψ) = Real",
      "notes": "Required field: target_Ψ (float)"
    },
    {
      "name": "target_psi_bounds",
      "expr": "target_Ψ >= 0 ∧ target_Ψ <= 1",
      "notes": "target_Ψ must be normalized"
    },
    {
      "name": "goalspec_has_optional_context",
      "expr": "has_field(GoalSpec, 'context') ∨ True",
      "notes": "Optional field: context (dict)"
    },
    {
      "name": "system_achieves_target_psi",
      "expr": "Ψ_achieved >= target_Ψ ∨ graceful_failure",
      "notes": "System must meet target or fail gracefully"
    }
  ]
}
```

---

## Guidelines

1. **Be Exhaustive**: Extract ALL constraints, even trivial ones
2. **Be Precise**: Use mathematical notation where possible
3. **Be Minimal**: One constraint per invariant (don't bundle)
4. **Name Well**: Use snake_case, descriptive names
5. **Annotate**: Add notes to clarify intent
6. **Validate**: Ensure output matches schema

---

## Template

```json
{
  "id": "{{CHUNK_ID}}",
  "title": "{{CHUNK_TITLE}}",
  "goalType": "{{GOAL_TYPE}}",
  "parameters": {
    "eightDimManifold": true,
    "scaleN": 100,
    "monsterPrimes": [2,3,5,7,11,13,17,19],
    "similarityObjective": "none"
  },
  "constraints": []
}
```
