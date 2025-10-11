{
  "id": "01",
  "title": "Executive Summary (Interface vs Intelligence)",
  "goalType": "proof",
  "parameters": {
    "eightDimManifold": true,
    "scaleN": 100,
    "monsterPrimes": [2,3,5,7,11,13,17,19],
    "similarityObjective": "none",
    "godelization": { "encode": false, "base": 10 }
  },
  "constraints": [
    {
      "name": "unitary_coords_exist",
      "expr": "true",
      "notes": "Reserve space for 8D coordinates; no extra domain constraints here."
    },
    {
      "name": "plan_exists_given_goal",
      "expr": "True",
      "notes": "Lean: existence of plan is proposition; MiniZinc: leave as satisfy baseline."
    }
  ]
}
