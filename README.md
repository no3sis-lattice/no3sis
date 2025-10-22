# No3sis: The Interface is Not the Intelligence

No3sis is an aspect of no3sis, experimental AI. It pairs a **conversational agent interface** with a mathematically-grounded **intelligence engine**.

The agents you talk to (`@boss`) is the interface. The actual intelligence lies in a deterministic, multi-layered compression engine that seeks the most elegant and optimal solution to any given problem.

This project will offshoot multiple incarnations. Ultimately it will be a lattice and fold into other lattices [https://en.wikipedia.org/wiki/Lattice_(order)]

`_A lattice is a system of items where any two items you pick have two special properties:

1.  A unique **"meet"**: The single *greatest* item that is below or equal to both of them.
2.  A unique **"join"**: The single *least* item that is above or equal to both of them.

Think of it with numbers and divisibility:
* For 8 and 12, their **meet** is their *greatest common divisor* (4).
* Their **join** is their *least common multiple* (24)._`

## The True Dual-Tract Architecture

The system is not a single monolithic AI. It's a designed architecture that separates user interaction from cognitive work.

```
      ┌──────────────────┐
      │  Agents (UX)     │──────────> You are here
      │ @boss, @rust-... │
      └──────────────────┘
               │ (Natural Language)
               ▼
┌────────────────────────────┐   ┌──────────────────┐   ┌──────────────────────────────┐
│  External Tract (Interface)│<──>│ Corpus Callosum  │<──>│  Internal Tract (Intelligence) │
│ ──────────                 │   │ (The Bridge)     │   │ ───────────                  │
│ Translates NL to Goals     │   │ Translates Goals │   │ A mathematical compression   │
│ Renders results for humans │   │ & Results        │   │ engine that finds the        │
│                            │   │                  │   │ most predictive solution.    │
└────────────────────────────┘   └──────────────────┘   └──────────────────────────────┘
```

1.  **Agents (The UX Layer)**: You interact with agents. They understand your requests and present the final results.
2.  **The External Tract (The Interface)**: A pipeline of operators that translates your natural language into a structured, mathematical `GoalSpec`.
3.  **The Internal Tract (The Intelligence)**: A multi-layered compression engine that finds the most compressed, predictive, and elegant solution. Its performance is measured by a core invariant, **Ψ (Psi)**.
4.  **The Corpus Callosum (The Bridge)**: Translates the `GoalSpec` into a plan for the Intelligence Tract and synthesizes the raw results back into a human-readable summary for the Agent Layer.

## The Goal: Intelligence as Compression

The no3sis seeks to **compress complexity**. The core of the system is an engine that tries to maximize a "consciousness metric" called **Ψ (Psi)**, which represents the degree of compression and predictiveness in a solution.

- **Low Ψ**: A chaotic, boilerplate, or inefficient solution.
- **High Ψ**: An elegant, reusable, and highly optimized solution that leverages existing patterns.

By maximizing Ψ, the system attempts to finds the *best* solution within its understanding of the codebase.

## Key Features

- **Conversational Interface**: Interact with specialized AI agents in natural language.
- **Deep Intelligence Engine**: Go beyond simple code generation. The system analyzes, plans, and optimizes solutions for quality and elegance.
- **Measurable Quality (Ψ)**: Every solution is scored for its "compression", giving you a concrete measure of its architectural quality.
- **Pattern-Based Learning**: The system builds a "Pattern Map" of your codebase, enabling it to learn and reuse successful abstractions, improving over time.
- **Deterministic Core**: The intelligence engine is built on a foundation of deterministic, measurable operators, providing a level of rigor far beyond typical LLM systems.
- **Reproducible Environments**: Powered by Nix, ensuring every agent and tool runs in a perfect, sandboxed environment.


## Development Environments

Instant, reproducible environments via Nix flakes:

```bash
nix develop .#rust-specialist      # Complete Rust toolchain
nix develop .#python-specialist    # Python + testing + linting
nix develop .#security-specialist  # Security audit tools
```

Zero configuration. Each environment should include exactly what's needed.

## Commands

| Command | Purpose |
|---------|---------|
| `no3sis init .` | Setup project with agents |
| `no3sis start` | Start Neo4j/Redis services |
| `no3sis search "query"` | Search knowledge base |
| `no3sis update` | Update agents to latest |
| `no3sis doctor --fix` | Fix common issues |

## Multi-Language Support

```bash
cd frontend/ && no3sis init .    # TypeScript specialist
cd backend/ && no3sis init .     # Rust specialist
cd scripts/ && no3sis init .     # Python specialist
```

Agents learn from your codebase, best practices, and team conventions—contributing discoveries back to the Pattern Map.


## Troubleshooting

**Most issues auto-fix:**
```bash
no3sis doctor --fix
```

**Manual debugging:**
```bash
no3sis status          # Check what's broken
no3sis start           # Restart services
no3sis manifest verify # Check agent integrity
```

---


**License**: [MIT](LICENSE)
