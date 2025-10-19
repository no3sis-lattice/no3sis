{
  description = "DevOps Engineer Agent with infrastructure and deployment tools";

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

          # Infrastructure as Code
          ansible
          jinja2
        ]);

        # DevOps tools environment
        devopsEnv = pkgs.buildEnv {
          name = "devops-engineer-env";
          paths = with pkgs; [
            # Core utilities
            git
            curl
            jq
            yq

            # Container tools
            docker
            docker-compose
            podman
            buildah

            # Kubernetes tools
            kubectl
            kubernetes-helm
            kustomize
            k9s
            kubectx

            # Infrastructure as Code
            terraform
            terragrunt
            ansible
            packer
            vagrant

            # Cloud CLI tools
            awscli2
            google-cloud-sdk
            azure-cli

            # Monitoring and observability
            prometheus
            grafana

            # CI/CD tools
            github-cli
            gitlab-runner

            # Configuration management
            consul
            vault

            # Networking
            dig
            netcat
            curl
            wget

            # System monitoring
            htop
            iotop
            lsof
          ];
        };

        # Agent script
        agentScript = pkgs.writeShellScript "devops-engineer-script" ''
          #!${pkgs.bash}/bin/bash
          set -euo pipefail

          AGENT_DIR="$HOME/.no3sis-system/.no3sis/agents/devops-engineer"

          if [[ ! -f "$AGENT_DIR/devops_engineer_agent.py" ]]; then
            echo "❌ DevOps Engineer agent not found at $AGENT_DIR"
            exit 1
          fi

          echo "🚀 Starting DevOps Engineer Agent..."
          cd "$AGENT_DIR"

          export PATH="${devopsEnv}/bin:$PATH"
          exec ${pythonEnv}/bin/python devops_engineer_agent.py "$@"
        '';

      in
      {
        packages = {
          devops-engineer = pkgs.writeShellScriptBin "devops-engineer" ''
            exec ${agentScript} "$@"
          '';

          default = self.packages.devops-engineer;
          devops-env = devopsEnv;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [ devopsEnv pythonEnv ];

          shellHook = ''
            echo "🚀 DevOps Engineer Development Environment"
            echo "Available tools:"
            echo "  - Containers: docker, podman, buildah"
            echo "  - Kubernetes: kubectl, helm, k9s"
            echo "  - IaC: terraform, ansible, packer"
            echo "  - Cloud: aws, gcloud, az"
            echo "  - Monitoring: prometheus, grafana"
            echo ""
            echo "To run the agent: devops-engineer"
          '';
        };

        checks = {
          devops-engineer-build = self.packages.devops-engineer;
        };
      }
    );
}
