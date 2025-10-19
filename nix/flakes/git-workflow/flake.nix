{
  description = "Git Workflow Agent with advanced Git tools and workflow automation";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Python environment for the agent runner
        pythonEnv = pkgs.python312.withPackages (ps: with ps; [
          # Core agent dependencies
          asyncio-mqtt
          aiofiles
          rich
          pyyaml

          # Synapse System integration
          neo4j
          redis
          numpy
          requests

          # Git integration
          GitPython
        ]);

        # Git workflow tools
        gitEnv = pkgs.buildEnv {
          name = "git-workflow-env";
          paths = with pkgs; [
            # Core Git
            git
            git-lfs

            # Git extensions
            git-delta
            git-absorb
            git-branchless
            git-recent
            git-trim

            # GitHub/GitLab integration
            github-cli
            gitlab-cli

            # Git workflow tools
            gitflow
            git-machete

            # Diff and merge tools
            difftastic
            meld

            # Commit tools
            commitizen
            gitlint

            # Branch management
            git-town

            # Code review
            reviewdog

            # Utilities
            jq
            yq
            curl
          ];
        };

        # Agent script
        agentScript = pkgs.writeShellScript "git-workflow-script" ''
          #!${pkgs.bash}/bin/bash
          set -euo pipefail

          AGENT_DIR="$HOME/.no3sis-system/.no3sis/agents/git-workflow"

          if [[ ! -f "$AGENT_DIR/git_workflow_agent.py" ]]; then
            echo "❌ Git Workflow agent not found at $AGENT_DIR"
            exit 1
          fi

          echo "🌳 Starting Git Workflow Agent..."
          cd "$AGENT_DIR"

          export PATH="${gitEnv}/bin:$PATH"
          exec ${pythonEnv}/bin/python git_workflow_agent.py "$@"
        '';

      in
      {
        packages = {
          git-workflow = pkgs.writeShellScriptBin "git-workflow" ''
            exec ${agentScript} "$@"
          '';

          default = self.packages.git-workflow;
          git-env = gitEnv;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [ gitEnv pythonEnv ];

          shellHook = ''
            echo "🌳 Git Workflow Development Environment"
            echo "Available Git tools:"
            echo "  - git-delta: Better diffs"
            echo "  - gh: GitHub CLI"
            echo "  - git-flow: Git flow workflow"
            echo "  - git-absorb: Auto-fixup commits"
            echo "  - commitizen: Conventional commits"
            echo ""
            echo "To run the agent: git-workflow"
          '';
        };

        checks = {
          git-workflow-build = self.packages.git-workflow;
        };
      }
    );
}
