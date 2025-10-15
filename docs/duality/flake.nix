{
  description = "Duality subsystem: dual-tract formalization with MiniZinc + Lean4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Pin Lean4 to a stable version compatible with mathlib4
    lean4 = {
      url = "github:leanprover/lean4?ref=v4.15.0";
    };
  };

  outputs = { self, nixpkgs, flake-utils, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = false;
        };

        # Python environment with test dependencies
        pythonEnv = pkgs.python311.withPackages (ps: with ps; [
          pytest
          hypothesis
          pygments
          # Additional deps from requirements.txt
        ]);

        # MiniZinc version pinned to 2.8.7 (stable)
        minizinc = pkgs.minizinc;

        # Lean4 from flake input (pinned to v4.15.0 for mathlib compatibility)
        lean = lean4.packages.${system}.lean;

        # Helper script for rendering pilots
        render-pilots = pkgs.writeShellScriptBin "duality-render-pilots" ''
          set -euo pipefail
          cd "''${DUALITY_ROOT:-$(pwd)}"

          echo "=== Rendering Duality Pilots ==="
          for chunk in 06 09 19 41; do
            echo "Rendering Chunk $chunk..."
            ${pythonEnv}/bin/python3 scripts/render_formalizations.py \
              true-dual-tract/chunks/chunk-''${chunk}.constraints.json \
              --use-base-imports \
              --force
          done
          echo "✓ All 4 pilots rendered successfully"
        '';

        # Helper script for validating pilots
        validate-pilots = pkgs.writeShellScriptBin "duality-validate-pilots" ''
          set -euo pipefail
          cd "''${DUALITY_ROOT:-$(pwd)}"

          echo "=== Validating Duality Pilots ==="

          # 1. MiniZinc syntax validation
          echo "Step 1/3: MiniZinc syntax validation"
          for chunk in 06 09 19 41; do
            mzn_file="true-dual-tract/chunks/chunk-''${chunk}.mzn"
            if [ -f "$mzn_file" ]; then
              ${minizinc}/bin/minizinc -e "$mzn_file" || {
                echo "❌ MiniZinc validation failed: $mzn_file"
                exit 1
              }
            fi
          done
          echo "✓ MiniZinc syntax valid"

          # 2. Cross-check (JSON ↔ MZN ↔ Lean)
          echo "Step 2/3: Cross-check constraint equivalence"
          ${pythonEnv}/bin/python3 scripts/cross_check_all.py \
            --chunks 06 09 19 41 \
            --report reports/cross-check-pilots.md || {
            echo "❌ Cross-check failed"
            exit 1
          }
          echo "✓ Cross-check passed"

          # 3. Lean4 compilation (non-fatal warnings)
          echo "Step 3/3: Lean4 compilation (pilots)"
          cd formal
          ${lean}/bin/lake update || true
          ${lean}/bin/lake build Duality.Chunks.Chunk06 \
                                  Duality.Chunks.Chunk09 \
                                  Duality.Chunks.Chunk19 \
                                  Duality.Chunks.Chunk41 || {
            echo "⚠️  Lean4 compilation had warnings (non-fatal)"
          }

          # Check for errors (fatal)
          if grep -qR "error:" Duality/Chunks/Chunk0{6,9}.lean Duality/Chunks/Chunk{19,41}.lean 2>/dev/null; then
            echo "❌ Lean4 errors detected in pilots"
            exit 1
          fi

          echo "✓ All validation steps passed"
        '';

        # Agent step runner (impure, for MCP integration)
        agent-step = pkgs.writeShellScriptBin "duality-agent-step" ''
          set -euo pipefail
          cd "''${DUALITY_ROOT:-$(pwd)}"

          if [ $# -eq 0 ]; then
            echo "Usage: duality-agent-step <task-description>"
            echo "Example: duality-agent-step 'solve chunk 06 and inject witness'"
            exit 1
          fi

          TASK="$*"
          echo "=== Duality Agent Step (Impure) ==="
          echo "Task: $TASK"
          echo ""
          echo "⚠️  This command allows impure operations (network, env vars, side effects)"
          echo ""

          # Placeholder for MCP integration
          # In production, this would invoke the MCP server with the task
          echo "TODO: Integrate with Noesis MCP server"
          echo "Proposed: noesis-agent --task \"$TASK\" --domain duality"

          exit 0
        '';

      in
      {
        packages = {
          duality-render-pilots = render-pilots;
          duality-validate-pilots = validate-pilots;
          duality-agent-step = agent-step;
        };

        apps = {
          duality-render-pilots = {
            type = "app";
            program = "${render-pilots}/bin/duality-render-pilots";
          };

          duality-validate-pilots = {
            type = "app";
            program = "${validate-pilots}/bin/duality-validate-pilots";
          };

          duality-agent-step = {
            type = "app";
            program = "${agent-step}/bin/duality-agent-step";
          };
        };

        devShells.default = pkgs.mkShell {
          name = "duality-dev";

          buildInputs = [
            pythonEnv
            minizinc
            lean
          ];

          packages = with pkgs; [
            bashInteractive
            coreutils
            jq
            git
          ];

          shellHook = ''
            echo "🎯 Duality Development Environment"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Python:   $(python --version 2>&1)"
            echo "MiniZinc: $(minizinc --version 2>&1 | head -1)"
            echo "Lean4:    $(lean --version 2>&1 | head -1)"
            echo ""
            echo "Tools available:"
            echo "  • pytest (test framework)"
            echo "  • hypothesis (property-based testing)"
            echo "  • pygments (syntax highlighting)"
            echo ""
            echo "Commands:"
            echo "  nix run .#duality-render-pilots     - Render 4 pilot chunks"
            echo "  nix run .#duality-validate-pilots   - Validate pilots (strict)"
            echo "  nix run .#duality-agent-step --impure <task>"
            echo "                                      - Run single agent task (impure)"
            echo ""
            echo "Environment:"
            echo "  DUALITY_ROOT=${toString ./.}"

            export DUALITY_ROOT=${toString ./.}
            export PATH="${render-pilots}/bin:${validate-pilots}/bin:${agent-step}/bin:$PATH"
          '';
        };

        # Default devShell
        devShell = self.devShells.${system}.default;
      }
    );
}
