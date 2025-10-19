{
  description = "Boss Agent - Pneuma orchestrator with full system control";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Python environment for the Synapse project manager with all dependencies
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

          # Project management tools
          jinja2
          toml
          GitPython

          # Development utilities
          click
          pathlib2
        ]);

        # Synapse System utilities
        synapseEnv = pkgs.buildEnv {
          name = "no3sis-system-env";
          paths = with pkgs; [
            # Core utilities
            curl
            jq
            git

            # Docker for service management
            docker
            docker-compose

            # Database tools
            redis
          ];
        };

        # Agent script that runs the actual Python implementation
        agentScript = pkgs.writeShellScript "boss-runner" ''
          #!${pkgs.bash}/bin/bash
          set -euo pipefail

          AGENT_DIR="$HOME/.no3sis-system/.no3sis/agents/boss"

          if [[ ! -f "$AGENT_DIR/boss_agent.py" ]]; then
            echo "❌ Boss agent not found at $AGENT_DIR"
            echo "Please ensure the Synapse System is properly initialized."
            exit 1
          fi

          echo "👑 Starting Boss Agent - Pneuma Orchestrator..."
          cd "$AGENT_DIR"

          # Add Synapse tools to PATH
          export PATH="${synapseEnv}/bin:$PATH"

          # Set Synapse environment variables
          export SYNAPSE_HOME="$HOME/.no3sis-system"
          export SYNAPSE_DATA_DIR="$SYNAPSE_HOME/.no3sis"
          export NEO4J_URI="bolt://localhost:7687"
          export NEO4J_USER="neo4j"
          export NEO4J_PASSWORD="password"
          export REDIS_URL="redis://localhost:6379"

          exec ${pythonEnv}/bin/python boss_agent.py "$@"
        '';

      in
      {
        packages = {
          boss = pkgs.writeShellScriptBin "boss" ''
            exec ${agentScript} "$@"
          '';

          default = self.packages.boss;

          # Full Synapse System environment
          synapse-env = synapseEnv;
        };

        # Development shell with Synapse System tools
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            pythonEnv
            synapseEnv

            # Additional development tools
            python312Packages.pip
            python312Packages.setuptools
            python312Packages.wheel
          ];

          shellHook = ''
            echo "👑 Boss Agent Development Environment"
            echo "Python version: $(python --version)"
            echo ""
            echo "Available tools:"
            echo "  - docker: Container management"
            echo "  - docker-compose: Multi-container applications"
            echo "  - redis-cli: Redis command line interface"
            echo "  - curl: HTTP client"
            echo "  - jq: JSON processor"
            echo "  - git: Version control"
            echo ""
            echo "Synapse System:"
            echo "  - Neo4j: bolt://localhost:7687"
            echo "  - Redis: redis://localhost:6379"
            echo ""
            echo "To run the agent: boss"
            echo "To start Synapse services: cd ~/.no3sis-system && docker-compose up -d"
            echo "To check Neo4j: curl http://localhost:7474"
            echo "To check Redis: redis-cli ping"
          '';

          # Set environment variables for Synapse development
          SYNAPSE_HOME = "$HOME/.no3sis-system";
          NEO4J_URI = "bolt://localhost:7687";
          REDIS_URL = "redis://localhost:6379";
        };

        # Checks to validate the agent and Synapse environment
        checks = {
          boss-build = self.packages.boss;

          synapse-dependencies-check = pkgs.runCommand "synapse-dependencies-check" {
            buildInputs = [ pythonEnv synapseEnv ];
          } ''
            echo "Checking Synapse dependencies..."
            python -c "import neo4j, redis, numpy; print('✅ Synapse dependencies available')"
            docker --version
            docker-compose --version
            redis-cli --version
            echo "✅ Synapse dependencies check passed"
            touch $out
          '';

          python-syntax-check = pkgs.runCommand "boss-syntax-check" {
            buildInputs = [ pythonEnv ];
          } ''
            AGENT_DIR="$HOME/.no3sis-system/.no3sis/agents/boss"
            if [[ -f "$AGENT_DIR/boss_agent.py" ]]; then
              echo "Checking Python syntax for Boss agent..."
              python -m py_compile "$AGENT_DIR/boss_agent.py"
              echo "✅ Python syntax check passed"
            else
              echo "⚠️  Agent file not found, skipping syntax check"
            fi
            touch $out
          '';
        };
      }
    );
}
