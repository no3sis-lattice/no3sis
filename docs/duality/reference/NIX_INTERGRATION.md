
# Duality under Nix (Quick Start)

Goals
- Use Nix to manage all tools (MiniZinc, Lean, Python) for Duality.
- Provide nix run apps for: render, validate, and a single impure step (agent/LLM hook).
- Keep CI reproducible: jobs run inside nix develop shell.

Prereqs
- nix, flakes enabled.

Enter shell
```bash
nix develop .#duality-shell
# Tools now available: minizinc, lean/lake, python3, jq, git
```

Apps
```bash
# Render pilots (impure not needed)
nix run .#duality-render-pilots

# Full validation (wrapped; non-fatal Lean exit, strict pilot cross-check)
nix run .#duality-validate

# Impure step (e.g., LLM agent single action, network/filesystem ok)
nix run .#duality-agent-step --impure -- --task "extract_constraints" --chunk 06
```

CI pattern
- In Actions:
  - nix develop .#duality-shell --command <your commands>
  - Or nix run apps above.
- Don’t rely on pre-checked-in .mzn: render in CI before MiniZinc/Lean validation.
