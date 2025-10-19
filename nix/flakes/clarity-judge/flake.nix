{
  description = "Clarity Judge Agent with code quality and complexity analysis tools";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        pythonEnv = pkgs.python312.withPackages (ps: with ps; [
          asyncio-mqtt aiofiles rich pyyaml neo4j redis numpy requests
          radon mccabe vulture pyflakes
        ]);

        clarityEnv = pkgs.buildEnv {
          name = "clarity-judge-env";
          paths = with pkgs; [
            git curl jq
            # Code complexity analysis
            cloc scc tokei
            # Code quality tools
            shellcheck yamllint
            # Documentation analysis
            aspell hunspell
          ];
        };

        agentScript = pkgs.writeShellScript "clarity-judge-script" ''
          AGENT_DIR="$HOME/.no3sis-system/.no3sis/agents/clarity-judge"
          [[ -f "$AGENT_DIR/clarity_judge_agent.py" ]] || { echo "Agent not found"; exit 1; }
          echo "⚖️ Starting Clarity Judge Agent..."
          cd "$AGENT_DIR"
          export PATH="${clarityEnv}/bin:$PATH"
          exec ${pythonEnv}/bin/python clarity_judge_agent.py "$@"
        '';

      in {
        packages = {
          clarity-judge = pkgs.writeShellScriptBin "clarity-judge" ''exec ${agentScript} "$@"'';
          default = self.packages.clarity-judge;
        };
        devShells.default = pkgs.mkShell {
          buildInputs = [ clarityEnv pythonEnv ];
          shellHook = ''
            echo "⚖️ Clarity Judge Development Environment"
            echo "Tools: radon, mccabe, cloc, shellcheck"
          '';
        };
        checks.clarity-judge-build = self.packages.clarity-judge;
      }
    );
}
