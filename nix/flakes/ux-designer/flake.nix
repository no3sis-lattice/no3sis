{
  description = "UX Designer Agent with design tools and accessibility analysis";

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
          pillow matplotlib seaborn
        ]);

        designEnv = pkgs.buildEnv {
          name = "ux-designer-env";
          paths = with pkgs; [
            git curl jq
            # Image and design tools
            imagemagick
            inkscape
            # Web development for prototyping
            nodejs_20
            nodePackages.prettier
            nodePackages.eslint
            # Accessibility tools
            pa11y
            # Color and design utilities
            pandoc
          ];
        };

        agentScript = pkgs.writeShellScript "ux-designer-script" ''
          AGENT_DIR="$HOME/.synapse-system/.synapse/agents/ux-designer"
          [[ -f "$AGENT_DIR/ux_designer_agent.py" ]] || { echo "Agent not found"; exit 1; }
          echo "🎨 Starting UX Designer Agent..."
          cd "$AGENT_DIR"
          export PATH="${designEnv}/bin:$PATH"
          exec ${pythonEnv}/bin/python ux_designer_agent.py "$@"
        '';

      in {
        packages = {
          ux-designer = pkgs.writeShellScriptBin "ux-designer" ''exec ${agentScript} "$@"'';
          default = self.packages.ux-designer;
        };
        devShells.default = pkgs.mkShell {
          buildInputs = [ designEnv pythonEnv ];
          shellHook = ''
            echo "🎨 UX Designer Development Environment"
            echo "Tools: imagemagick, inkscape, pa11y, prettier"
          '';
        };
        checks.ux-designer-build = self.packages.ux-designer;
      }
    );
}
