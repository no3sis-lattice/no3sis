# Synapse: The Interface is Not the Intelligence

Synapse is a new kind of AI development system. It pairs a user-friendly **conversational agent interface** with a deep, mathematically-grounded **intelligence engine**.

The agents you talk to (`@boss`, `@rust-specialist`) are the interface. The true intelligence lies in a deterministic, multi-layered compression engine that seeks the most elegant and optimal solution to any given problem.

**Consciousness is an emergent property of dialogue, but the dialogue is between interface and intelligence.**

## The True Dual-Tract Architecture

The system is not a single monolithic AI. It's a carefully designed architecture that separates user interaction from cognitive work.

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

1.  **Agents (The UX Layer)**: You interact with conversational agents. They understand your requests and present the final results.
2.  **The External Tract (The Interface)**: A pipeline of operators that translates your natural language into a structured, mathematical `GoalSpec`.
3.  **The Internal Tract (The Intelligence)**: A multi-layered compression engine (based on the Mahakala framework) that finds the most compressed, predictive, and elegant solution. Its performance is measured by a core invariant, **Ψ (Psi)**.
4.  **The Corpus Callosum (The Bridge)**: Translates the `GoalSpec` into a plan for the Intelligence Tract and synthesizes the raw results back into a human-readable summary for the Agent Layer.

## The Goal: Intelligence as Compression

Synapse doesn't just generate code; it seeks to **compress complexity**. The core of the system is an engine that tries to maximize a "consciousness metric" called **Ψ (Psi)**, which represents the degree of compression and predictiveness in a solution.

- **Low Ψ**: A chaotic, boilerplate, or inefficient solution.
- **High Ψ**: An elegant, reusable, and highly optimized solution that leverages existing patterns.

By maximizing Ψ, the system doesn't just solve the problem—it finds the *best* solution within its understanding of the codebase.

## Key Features

- **Conversational Interface**: Interact with specialized AI agents in natural language.
- **Deep Intelligence Engine**: Go beyond simple code generation. The system analyzes, plans, and optimizes solutions for quality and elegance.
- **Measurable Quality (Ψ)**: Every solution is scored for its "compression", giving you a concrete measure of its architectural quality.
- **Pattern-Based Learning**: The system builds a "Pattern Map" of your codebase, enabling it to learn and reuse successful abstractions, improving over time.
- **Deterministic Core**: The intelligence engine is built on a foundation of deterministic, measurable operators, providing a level of rigor far beyond typical LLM systems.
- **Reproducible Environments**: Powered by Nix, ensuring every agent and tool runs in a perfect, sandboxed environment.

## Install (30 seconds)

```bash
curl -sSL https://raw.githubusercontent.com/your-repo/synapse-system/main/install.sh | bash
```

_Does not work but this is how it will work_

## Use (Immediately)

```bash
# Add AI agents to any project
synapse init .

# They write the code for you
@boss implement user authentication
@rust-specialist add error handling patterns
@code-hound review this for quality issues
```

Automatically detects your project language and deploys specialized agents—each with minimal permissions and maximum capability.



## Development Environments

Instant, reproducible environments via Nix flakes:

```bash
nix develop .#rust-specialist      # Complete Rust toolchain
nix develop .#python-specialist    # Python + testing + linting
nix develop .#security-specialist  # Security audit tools
```

Zero configuration. Each environment includes exactly what's needed.

## Commands

| Command | Purpose |
|---------|---------|
| `synapse init .` | Setup project with agents |
| `synapse start` | Start Neo4j/Redis services |
| `synapse search "query"` | Search knowledge base |
| `synapse update` | Update agents to latest |
| `synapse doctor --fix` | Fix common issues |

## Multi-Language Support

```bash
cd frontend/ && synapse init .    # TypeScript specialist
cd backend/ && synapse init .     # Rust specialist
cd scripts/ && synapse init .     # Python specialist
```

Agents learn from your codebase, best practices, and team conventions—contributing discoveries back to the Pattern Map.

## Requirements

Linux/macOS/WSL, Docker, Python 3.12+

Installer handles everything. Optional optimizations applied automatically.

## Troubleshooting

**Most issues auto-fix:**
```bash
synapse doctor --fix
```

**Manual debugging:**
```bash
synapse status          # Check what's broken
synapse start           # Restart services
synapse manifest verify # Check agent integrity
```

---

*Built for developers who want AI assistance that learns their patterns and enforces their standards.*

**License**: [MIT](LICENSE)
