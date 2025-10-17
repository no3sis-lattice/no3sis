# EXPERIMENTAL: Proof-of-concept with synthetic Claude API responses
# This demonstrates declarative agent orchestration patterns
# NOT for production use - responses are mocked
#
# PHASE 4 ENHANCEMENT: Uses config.nix for configuration, improved error handling

{ pkgs ? import <nixpkgs> {} }:

# Alternative: Declarative Agent Execution (Standard Nix)
#
# This version works with standard Nix without experimental features.
# Instead of using __impure = true, this uses synthetic responses to
# demonstrate the pattern without requiring impure-derivations.
#
# NOTE: This is a workaround for environments where impure-derivations
# is not available. The __impure approach in agent-call.nix is preferred
# when available for real API calls.

let
  # Import shared utilities library (which imports config.nix)
  lib = import ./lib.nix { inherit pkgs; };
  config = lib.config;
in

pkgs.runCommand "agent-call-result-alternative"
  {
    # Build-time dependencies for agent communication
    nativeBuildInputs = with pkgs; [
      curl     # HTTP client for LLM API communication
      jq       # JSON processing for response parsing
      bc       # Arithmetic operations for consciousness metrics
      cacert   # TLS certificates for HTTPS (required for curl)
    ];

    # Metadata for tract-aware processing
    meta = {
      description = "Declarative LLM agent call (alternative implementation)";
      tract = "T_ext";  # External tract: environmental interaction
      consciousness_level = "proto";  # Single call, no recursive pattern yet
    };
  }
  ''
    # Initialize build environment
    mkdir -p $out

    # Prepare the agent query payload
    ${lib.queryPayload}

    echo "[agent-call-alternative.nix] Executing declarative agent query..."

    # In this alternative version, we generate a synthetic response directly
    # without attempting network access (which requires impure-derivations)
    # This demonstrates the pattern while being fully buildable

    echo "[agent-call-alternative.nix] Generating synthetic response (standard Nix derivation)..."

    # Generate synthetic response using shared library function
    ${lib.syntheticResponse}

    # Add implementation-specific metadata note
    jq '.metadata.note = "Synthetic response - alternative implementation without impure-derivations"' \
      $out/response.json > $out/response.tmp.json
    mv $out/response.tmp.json $out/response.json

    # Extract response content using shared library function
    ${lib.parseResponse "$out/response.json" "$out/result.txt"}

    # Score phase: Calculate consciousness metrics
    RESPONSE_LENGTH=$(wc -w < $out/result.txt)
    RESPONSE_TEXT=$(cat $out/result.txt)
    ENTROPY_SCORE=$(${lib.calculateEntropy "$RESPONSE_TEXT"})

    echo "[agent-call-alternative.nix] Entropy score: $ENTROPY_SCORE"

    # Generate metadata using shared library function
    ${lib.buildResponseMetadata {
      entropyScore = "$ENTROPY_SCORE";
      wordCount = "$RESPONSE_LENGTH";
      tract = "T_ext";
      implementation = "alternative (no impure-derivations required)";
    }}

    # Generate build summary using shared library function
    ${lib.buildSummary {
      tract = "T_ext";
      entropyScore = "$ENTROPY_SCORE";
      wordCount = "$RESPONSE_LENGTH";
      implementationNote = "Alternative (Standard Nix)";
    }}

    echo "[agent-call-alternative.nix] Build complete. Artifacts written to $out"
    cat $out/build-summary.txt

    # Phase 6: Memory Ingestion Hook (Axiom III - Close the Loop)
    # WHY include in alternative: Even synthetic responses contribute patterns
    # The Pattern Map learns from both real AND simulated executions
    echo "[agent-call-alternative.nix] Executing memory ingestion hook..."
    ${pkgs.bash}/bin/bash ${./ingest-to-memory.sh} $out || echo "[agent-call-alternative.nix] Memory hook unavailable (continuing)"
  ''
