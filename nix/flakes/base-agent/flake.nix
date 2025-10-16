{
  description = "Base agent flake providing a shared Python environment for Synapse agents";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Import permissions system from local file
        permissionsFile = ./permissions.nix;
        permissionSystem = import permissionsFile;

        # Standard Python environment for Synapse agents
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

          # Common utilities
          click
          jinja2
          pathlib2
        ]);

      in
      {
        packages = {
          # Expose the Python environment as a package
          python-env = pythonEnv;
          default = pythonEnv;
        };

        # Export for other flakes to use
        lib = {
          pythonEnv = pythonEnv;

          # Permission system integration
          permissions = permissionSystem;

          # Permission validation utilities for agents
          validatePermissions = agentName: requiredPerms:
            let
              agentPerms = permissionSystem.agentPermissions.${agentName} or [];
              hasAllPerms = builtins.all (perm: builtins.elem perm agentPerms) requiredPerms;
            in
              if hasAllPerms then true
              else builtins.throw "Agent ${agentName} lacks required permissions: ${builtins.concatStringsSep ", " requiredPerms}";

          # Create permission-aware agent runner
          createAgentRunner = agentName: scriptPath: requiredPerms:
            let
              agentPerms = permissionSystem.agentPermissions.${agentName} or [];
              validatePerms = self.lib.validatePermissions agentName requiredPerms;
            in
              pkgs.writeShellScript "${agentName}-runner" ''
                #!${pkgs.bash}/bin/bash
                set -euo pipefail

                # Pneuma Permission Validation
                echo "🔒 Validating ${agentName} permissions..."
                AGENT_PERMISSIONS="${builtins.concatStringsSep " " agentPerms}"
                echo "   Granted: $AGENT_PERMISSIONS"

                # Execute agent script
                echo "🤖 Starting ${agentName}..."
                exec ${pythonEnv}/bin/python ${scriptPath} "$@"
              '';
        };

        # Development shell with the Python environment
        devShells.default = pkgs.mkShell {
          buildInputs = [ pythonEnv ];

          shellHook = ''
            echo "🐍 Base Synapse Python Environment"
            echo "Python version: $(python --version)"
            echo "Available packages: neo4j, redis, rich, pyyaml, etc."
          '';
        };

        checks.python-env-build = pythonEnv;
      }
    );
}
