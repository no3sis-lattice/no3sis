{
  description = "Security Specialist Agent with comprehensive security scanning tools";

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

          # Security analysis
          bandit
          safety
          cryptography
        ]);

        # Security scanning tools
        securityEnv = pkgs.buildEnv {
          name = "security-specialist-env";
          paths = with pkgs; [
            # Core utilities
            git
            curl
            jq

            # Secret scanning
            gitleaks
            truffleHog

            # Vulnerability scanning
            trivy
            grype

            # Code analysis
            semgrep
            codeql

            # Network security
            nmap
            masscan

            # Container security
            cosign
            syft

            # Static analysis
            shellcheck
            yamllint

            # Cryptography tools
            openssl
            age
            gnupg
          ];
        };

        # Agent script
        agentScript = pkgs.writeShellScript "security-specialist-script" ''
          #!${pkgs.bash}/bin/bash
          set -euo pipefail

          AGENT_DIR="$HOME/.no3sis-system/.no3sis/agents/security-specialist"

          if [[ ! -f "$AGENT_DIR/security_specialist_agent.py" ]]; then
            echo "❌ Security Specialist agent not found at $AGENT_DIR"
            exit 1
          fi

          echo "🔒 Starting Security Specialist Agent..."
          cd "$AGENT_DIR"

          export PATH="${securityEnv}/bin:$PATH"
          exec ${pythonEnv}/bin/python security_specialist_agent.py "$@"
        '';

      in
      {
        packages = {
          security-specialist = pkgs.writeShellScriptBin "security-specialist" ''
            exec ${agentScript} "$@"
          '';

          default = self.packages.security-specialist;
          security-env = securityEnv;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [ securityEnv pythonEnv ];

          shellHook = ''
            echo "🔒 Security Specialist Development Environment"
            echo "Available security tools:"
            echo "  - gitleaks: Secret detection"
            echo "  - trivy: Vulnerability scanner"
            echo "  - semgrep: Static analysis"
            echo "  - nmap: Network scanning"
            echo "  - bandit: Python security linter"
            echo ""
            echo "To run the agent: security-specialist"
          '';
        };

        checks = {
          security-specialist-build = self.packages.security-specialist;
        };
      }
    );
}
