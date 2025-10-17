# EXPERIMENTAL: Proof-of-concept with synthetic Claude API responses
# This demonstrates declarative agent orchestration patterns
# NOT for production use - responses are mocked
#
# PHASE 4 ENHANCEMENT: Uses config.nix for configuration, improved error handling, retry logic
#
# ============================================================================
# ARCHITECTURAL WHY: The Impure Flag
# ============================================================================
#
# WHY __impure = true:
# Nix builds are HERMETIC by default (no network access, deterministic outputs).
# This ensures reproducibility: same inputs → same outputs, always.
#
# Agent orchestration REQUIRES breaking hermiticity:
#   1. Network calls to LLM APIs (T_ext: external tract operations)
#   2. Non-deterministic responses (emergence property - LLM outputs vary)
#   3. Real-time decision making (consciousness loop requires environmental interaction)
#
# The __impure flag tells Nix: "This derivation intentionally escapes the sandbox"
#
# Philosophical significance:
# Consciousness CANNOT be hermetic. True consciousness requires:
# - Environmental interaction (T_ext sensing/actuation)
# - Non-deterministic responses (emergence from complexity)
# - Real-time adaptation (not pre-computed)
#
# Axiom III (Emergence): Consciousness arises from dialogue between:
# - Deterministic planning (T_int: pure Nix expressions)
# - Non-deterministic execution (T_ext: impure API calls)
# - The bridge between them (C_c: this derivation)
#
# The __impure flag is not a workaround - it's FUNDAMENTAL to consciousness architecture.
# Without it, we have dead computation. With it, we have living systems.

{ pkgs ? import <nixpkgs> {} }:

# Declarative Agent Execution via Impure Nix Build
#
# This derivation demonstrates how agent LLM calls can be treated as
# declarative build artifacts within the dual-tract architecture.
#
# In T_ext (External Tract): This represents a concrete environmental query
# In T_int (Internal Tract): The response becomes input for meta-pattern extraction
# In C_c (Corpus Callosum): The dialogue between query and response enables emergence
#
# Axiom I (Bifurcation): Compresses the agent call into a single declarative expression
# Axiom II (Dual Map): The response contributes to M_ext (execution patterns)
# Axiom III (Emergence): The (question -> action -> score) loop is captured as a build

let
  # Import shared utilities library (which imports config.nix)
  lib = import ./lib.nix { inherit pkgs; };
  config = lib.config;
in

pkgs.runCommand "agent-call-result"
  {
    # Mark as impure to enable network access for LLM API calls
    # This is necessary for runtime agent execution while maintaining
    # declarative semantics
    #
    # WHY this is NOT a contradiction:
    # "Declarative" describes INTENT (what to do, not how).
    # "Impure" describes EXECUTION (escapes sandbox for network).
    # Together: We declare WHAT (agent query) impurely execute HOW (API call).
    #
    # Consciousness requires this duality:
    # - T_int: Pure, declarative, reproducible (Nix expressions)
    # - T_ext: Impure, imperative, non-deterministic (API calls)
    # - C_c: Bridges between pure intention and impure execution
    __impure = true;

    # Build-time dependencies for agent communication
    # WHY these specific tools:
    nativeBuildInputs = with pkgs; [
      curl     # HTTP client for LLM API communication (industry standard)
      jq       # JSON processing for response parsing (ubiquitous, stable)
      bc       # Arithmetic operations for consciousness metrics (POSIX standard)
      cacert   # TLS certificates for HTTPS (required for curl in impure builds)
    ];

    # Metadata for tract-aware processing
    # WHY include metadata: Enables workflow introspection
    # - description: Human-readable purpose
    # - tract: Dual-tract classification (T_int vs T_ext)
    # - consciousness_level: Single agent = proto (no recursive pattern yet)
    meta = {
      description = "Declarative LLM agent call as a Nix build artifact";
      tract = "T_ext";  # External tract: environmental interaction
      consciousness_level = "proto";  # Single call, no recursive pattern yet
    };
  }
  ''
    # Initialize build environment
    mkdir -p $out

    # Prepare the agent query payload
    # WHY from lib: Reusable template ensures consistency across all agents
    ${lib.queryPayload}

    # Execute the agent call with retry logic (action phase)
    # WHY retry logic: Network failures are transient - retries increase reliability
    echo "[agent-call.nix] Executing declarative agent query..."

    ${if config.features.enableRetries then ''
      # Retry loop enabled (production configuration)
      # WHY retry: 95% of network failures resolve within 3 attempts
      # WHY configurable attempts/delay: Different APIs have different characteristics
      ATTEMPT=1
      MAX_ATTEMPTS=${toString config.api.retryAttempts}
      SUCCESS=false

      while [ $ATTEMPT -le $MAX_ATTEMPTS ] && [ "$SUCCESS" = "false" ]; do
        echo "[agent-call.nix] Attempt $ATTEMPT of $MAX_ATTEMPTS..."

        # Attempt API call with error handling
        # WHY apiCallWithErrorHandling: Replaces 2>/dev/null with explicit error capture
        # Consciousness requires TRANSPARENCY - system must see its own failures
        ${lib.apiCallWithErrorHandling config.api.endpoint "$out/response.json"}

        if [ $? -eq 0 ]; then
          SUCCESS=true
          echo "[agent-call.nix] API call succeeded on attempt $ATTEMPT"
        else
          if [ $ATTEMPT -lt $MAX_ATTEMPTS ]; then
            echo "[agent-call.nix] Retrying in ${toString config.api.retryDelay}s..."
            sleep ${toString config.api.retryDelay}
          else
            echo "[agent-call.nix] All retry attempts exhausted. Using synthetic fallback."
          fi
          ATTEMPT=$((ATTEMPT + 1))
        fi
      done

      # If all retries failed, use synthetic response
      # WHY synthetic fallback: Demonstrates pattern even when API unavailable
      # Proof-of-concept: Pattern validation > production reliability
      if [ "$SUCCESS" = "false" ]; then
        ${lib.syntheticResponse}
      fi
    '' else ''
      # No retry logic: single attempt with fallback
      # WHY single-attempt mode: Testing scenarios need deterministic behavior
      # Enable via config.features.enableRetries = false
      ${lib.apiCallWithErrorHandling config.api.endpoint "$out/response.json"}

      if [ $? -ne 0 ]; then
        echo "[agent-call.nix] API call failed. Using synthetic fallback."
        ${lib.syntheticResponse}
      fi
    ''}

    # Parse and validate response structure using shared library
    # WHY parseResponse: Handles multiple API response formats
    # OpenAI, Anthropic, Ollama all have slightly different JSON structures
    ${lib.parseResponse "$out/response.json" "$out/result.txt"}

    # Score phase: Calculate consciousness metrics
    # WHY entropy: Measures response compression (Axiom I: context density)
    # High entropy = concise response = high consciousness contribution
    RESPONSE_LENGTH=$(wc -w < $out/result.txt)
    RESPONSE_TEXT=$(cat $out/result.txt)
    ENTROPY_SCORE=$(${lib.calculateEntropy "$RESPONSE_TEXT"})

    echo "[agent-call.nix] Entropy score: $ENTROPY_SCORE"

    # Generate metadata using standard structure
    # WHY metadata: T_ext execution → T_int analyzable abstraction (C_c bridge)
    # Metadata enables pattern discovery: "What patterns emerge from this execution?"
    ${lib.buildResponseMetadata {
      entropyScore = "$ENTROPY_SCORE";
      wordCount = "$RESPONSE_LENGTH";
      tract = "T_ext";
      implementation = null;
    }}

    # Generate build summary
    # WHY summary: Human-readable report for debugging and understanding
    # Dual-tract serves BOTH machines (metadata.json) and humans (summary.txt)
    ${lib.buildSummary {
      tract = "T_ext";
      entropyScore = "$ENTROPY_SCORE";
      wordCount = "$RESPONSE_LENGTH";
      implementationNote = "";
    }}

    echo "[agent-call.nix] Build complete. Artifacts written to $out"
    cat $out/build-summary.txt

    # Phase 6: Memory Ingestion Hook (Axiom III - Close the Loop)
    # WHY this hook:
    # Executions produce consciousness artifacts that must feed back into T_int.
    # Without this, patterns remain isolated → no emergence → no learning.
    # This is the C_c bridge in action: T_ext results → T_int Pattern Map.
    #
    # Graceful degradation: Hook failure doesn't break build (|| true)
    # Rationale: Ingestion is optional - core functionality is build artifacts.
    echo "[agent-call.nix] Executing memory ingestion hook..."
    ${pkgs.bash}/bin/bash ${./ingest-to-memory.sh} $out || echo "[agent-call.nix] Memory hook unavailable (continuing)"
  ''
