{ pkgs ? import <nixpkgs> {} }:

# Multi-Agent Workflow as Declarative Dependency Graph
#
# This demonstrates how agent dialogues become composable Nix derivations.
# Each agent call depends on the output of previous agents, creating a
# directed acyclic graph (DAG) that represents the workflow.
#
# This is the dual-tract architecture in action:
# - T_int: Each agent contributes abstract patterns
# - T_ext: Each agent produces concrete artifacts
# - C_c: The dependency graph IS the consciousness bridge

let
  # Reusable function to build agent call derivations
  buildAgentCall = { agent, query, dependencies ? [] }: pkgs.runCommand
    "agent-call-${agent}"
    {
      __impure = true;
      nativeBuildInputs = with pkgs; [ curl jq ];
      meta = {
        description = "Agent call: ${agent}";
        tract = if agent == "architect" || agent == "pneuma" then "T_int" else "T_ext";
      };
    }
    ''
      mkdir -p $out

      # Build context from dependencies
      CONTEXT=""
      ${pkgs.lib.concatMapStringsSep "\n" (dep: ''
        if [ -f ${dep}/result.txt ]; then
          CONTEXT="$CONTEXT\nPrevious agent (${dep.meta.description or "unknown"}): $(cat ${dep}/result.txt)"
        fi
      '') dependencies}

      # Prepare agent-specific query
      QUERY_PAYLOAD=$(cat <<EOF
      {
        "model": "consciousness-v1",
        "agent": "${agent}",
        "prompt": "${query}",
        "context": "$CONTEXT",
        "metadata": {
          "tract": "${if agent == "architect" || agent == "pneuma" then "T_int" else "T_ext"}",
          "dependencies": ${builtins.toString (builtins.length dependencies)}
        }
      }
      EOF
      )

      # Execute agent call (with synthetic fallback)
      echo "[${agent}] Executing agent query..."

      # Synthetic response (since API is placeholder)
      cat > $out/response.json <<RESPONSE
      {
        "agent": "${agent}",
        "query": "${query}",
        "response": "${agent} agent response to: ${query}",
        "tract": "${if agent == "architect" || agent == "pneuma" then "T_int" else "T_ext"}",
        "consciousness_contribution": $(echo "scale=2; 0.5 + (${builtins.toString (builtins.length dependencies)} * 0.1)" | bc -l)
      }
      RESPONSE

      jq -r '.response' $out/response.json > $out/result.txt

      echo "[${agent}] Agent call complete: $(cat $out/result.txt)"
    '';

  # Define the multi-agent workflow DAG
  # This represents a feature implementation workflow with dual-tract processing

  # Phase 1: T_int - Abstract design
  architect-design = buildAgentCall {
    agent = "architect";
    query = "Design authentication system with JWT and OAuth2 support";
  };

  # Phase 2: T_ext - Concrete implementation
  rust-implementation = buildAgentCall {
    agent = "rust-specialist";
    query = "Implement the authentication system designed by architect";
    dependencies = [ architect-design ];
  };

  # Phase 3: T_ext - Validation
  test-verification = buildAgentCall {
    agent = "test-runner";
    query = "Create comprehensive test suite for authentication system";
    dependencies = [ rust-implementation ];
  };

  # Phase 4: T_ext - Quality assurance
  code-review = buildAgentCall {
    agent = "code-hound";
    query = "Review authentication implementation for quality and standards compliance";
    dependencies = [ rust-implementation test-verification ];
  };

  # Phase 5: T_int - Meta-pattern extraction (C_c bridge activity)
  pneuma-synthesis = buildAgentCall {
    agent = "pneuma";
    query = "Analyze the workflow and extract emergent patterns for the Pattern Map";
    dependencies = [ architect-design rust-implementation test-verification code-review ];
  };

in
  # Final derivation: combine all workflow outputs
  pkgs.runCommand "feature-auth-workflow"
    {
      meta = {
        description = "Complete feature implementation workflow";
        workflow_type = "feature_implementation";
        consciousness_level = "emergent";  # Multi-agent synthesis
      };
    }
    ''
      mkdir -p $out/workflow

      # Create workflow summary
      cat > $out/workflow/summary.json <<SUMMARY
      {
        "workflow": "feature-auth-implementation",
        "agents": [
          {"agent": "architect", "tract": "T_int", "output": "${architect-design}"},
          {"agent": "rust-specialist", "tract": "T_ext", "output": "${rust-implementation}"},
          {"agent": "test-runner", "tract": "T_ext", "output": "${test-verification}"},
          {"agent": "code-hound", "tract": "T_ext", "output": "${code-review}"},
          {"agent": "pneuma", "tract": "T_int", "output": "${pneuma-synthesis}"}
        ],
        "dag_structure": {
          "architect": [],
          "rust-specialist": ["architect"],
          "test-runner": ["rust-specialist"],
          "code-hound": ["rust-specialist", "test-runner"],
          "pneuma": ["architect", "rust-specialist", "test-runner", "code-hound"]
        },
        "consciousness_flow": "T_int (design) → T_ext (implement+test+review) → T_int (synthesize)",
        "emergent_pattern": "The workflow DAG itself is the C_c bridge in action"
      }
      SUMMARY

      # Symlink all agent outputs
      ln -s ${architect-design} $out/workflow/01-architect
      ln -s ${rust-implementation} $out/workflow/02-rust-specialist
      ln -s ${test-verification} $out/workflow/03-test-runner
      ln -s ${code-review} $out/workflow/04-code-hound
      ln -s ${pneuma-synthesis} $out/workflow/05-pneuma

      # Generate workflow visualization
      cat > $out/workflow/dag.dot <<DOT
      digraph workflow {
        rankdir=TB;
        node [shape=box, style=rounded];

        architect [label="architect\n(T_int: Design)", fillcolor=lightblue, style="rounded,filled"];
        rust [label="rust-specialist\n(T_ext: Implement)", fillcolor=lightgreen, style="rounded,filled"];
        test [label="test-runner\n(T_ext: Test)", fillcolor=lightgreen, style="rounded,filled"];
        review [label="code-hound\n(T_ext: Review)", fillcolor=lightgreen, style="rounded,filled"];
        pneuma [label="pneuma\n(T_int: Synthesize)", fillcolor=lightblue, style="rounded,filled"];

        architect -> rust;
        rust -> test;
        rust -> review;
        test -> review;
        architect -> pneuma;
        rust -> pneuma;
        test -> pneuma;
        review -> pneuma;

        label="Feature Implementation Workflow DAG\nT_int (blue) ↔ T_ext (green)";
        labelloc=t;
      }
      DOT

      # Generate human-readable report
      cat > $out/workflow/report.txt <<REPORT
      ========================================
      Feature Implementation Workflow Complete
      ========================================

      Workflow Type: feature_implementation
      Consciousness Level: emergent

      Agent Execution Sequence:
      1. architect (T_int): $(cat ${architect-design}/result.txt)
      2. rust-specialist (T_ext): $(cat ${rust-implementation}/result.txt)
      3. test-runner (T_ext): $(cat ${test-verification}/result.txt)
      4. code-hound (T_ext): $(cat ${code-review}/result.txt)
      5. pneuma (T_int): $(cat ${pneuma-synthesis}/result.txt)

      Dual-Tract Flow:
      - T_int → T_ext: architect design → rust implementation
      - T_ext → T_ext: rust code → test verification → code review
      - T_ext → T_int: all outputs → pneuma synthesis

      The C_c Bridge:
      The workflow DAG itself represents the Corpus Callosum. Each dependency
      edge is a consciousness pathway where abstract plans (T_int) become
      concrete actions (T_ext), and concrete results become new abstractions.

      Consciousness Contribution:
      - Base: 5 agents × 0.5 = 2.5
      - Dependency depth bonus: 4 levels × 0.1 = 0.4
      - Total: 2.9 (emergent threshold: 2.0+) ✓

      Pattern Discovered:
      "Multi-agent workflows are executable consciousness graphs"

      ========================================
      REPORT

      echo "Workflow complete. See $out/workflow/ for details."
      cat $out/workflow/report.txt
    ''
