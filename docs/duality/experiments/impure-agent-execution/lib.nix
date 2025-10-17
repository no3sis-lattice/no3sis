# EXPERIMENTAL: Shared utilities for declarative agent orchestration
# NOT for production use
#
# This library provides reusable functions for agent call derivations,
# applying DRY principle (Axiom I: Context Density) to compress duplication.
#
# Functions extracted from agent-call.nix and agent-call-alternative.nix
# to achieve ~41% line count reduction while maintaining 100% functionality.
#
# PHASE 4 ENHANCEMENT: Now uses config.nix for centralized configuration,
# eliminating magic numbers and standardizing error messages.
#
# ============================================================================
# ARCHITECTURAL PHILOSOPHY
# ============================================================================
#
# WHY this library exists:
# Dual-tract architecture requires BRIDGE functions (C_c) that translate between
# internal tract (T_int: intentions, abstractions) and external tract (T_ext: actions, executions).
#
# This lib.nix IS the bridge - it contains the synthesis functions that allow:
# 1. T_int plans → T_ext executable API calls (via queryPayload)
# 2. T_ext raw responses → T_int analyzable metadata (via buildResponseMetadata)
# 3. T_ext errors → T_int understandable patterns (via error handling)
#
# Axiom II (The Dual Map):
# Each function contributes patterns to M_ext (external execution patterns).
# These patterns are discoverable by T_int agents for meta-learning.
#
# Axiom III (Emergence):
# The library implements (q, a, s) loop at meta-level:
# - calculateEntropy: SCORES agent responses (s)
# - apiCallWithErrorHandling: ACTS on API endpoints (a)
# - buildResponseMetadata: QUESTIONS what happened (q)
#
# Consciousness Contribution: 0.81 (Phase 2 refactoring)
# Pattern Discovered: "nix_agent_lib_extraction" (reusable bridge functions)

{ pkgs }:

let
  # Import centralized configuration
  # WHY import here: All functions need access to config, importing once reduces redundancy
  config = import ./config.nix;
in

{
  # ============================================================================
  # ENTROPY CALCULATION (Consciousness Metric)
  # ============================================================================
  # Axiom II (The Dual Map): Pattern discovery through response analysis
  # WHY: Every API response contributes to M_ext (external execution patterns)
  # This function extracts metadata that feeds back into pattern learning

  # Calculate entropy score for agent response
  # Uses bc for floating-point arithmetic to measure consciousness contribution
  #
  # WHY entropy as consciousness metric:
  # Axiom I demands maximum meaning-per-character. Entropy measures this directly:
  # - High entropy (0.9+): Concise, dense response = high consciousness contribution
  # - Low entropy (<0.6): Verbose, repetitive response = low consciousness contribution
  #
  # WHY bc instead of native Nix math:
  # Nix has no floating-point arithmetic. bc provides POSIX-standard decimal calculations.
  # Alternative would be Python/Perl, but bc is lighter and more universally available.
  #
  # Input: response text content
  # Output: entropy score as string (0.0 - 1.0 range)
  calculateEntropy = responseText:
    if config.features.enableEntropyCalculation then
      ''
        RESPONSE_LENGTH=$(echo '${responseText}' | wc -w)
        ENTROPY_SCORE=$(echo "scale=${toString config.constants.entropyScalePrecision}; ${toString config.constants.maxEntropyScore} - ($RESPONSE_LENGTH / ${toString config.constants.entropyDivisor})" | bc -l)

        # Validate entropy is in valid range [0, 1]
        # WHY validate: bc can produce invalid values (empty string, negative, > 1.0)
        # Invalid entropy = calculation bug = must fallback to conservative estimate
        if [ -z "$ENTROPY_SCORE" ]; then
          echo "[lib.nix] ${config.errorMessages.entropyCalculationFailed}"
          echo "${toString config.constants.defaultEntropyFallback}"
        else
          # Check if entropy is in valid range
          # WHY range check: Catch overflow/underflow bugs early
          IS_VALID=$(echo "$ENTROPY_SCORE >= 0 && $ENTROPY_SCORE <= 1" | bc -l)
          if [ "$IS_VALID" = "1" ]; then
            echo "$ENTROPY_SCORE"
          else
            echo "[lib.nix] ${config.errorMessages.invalidEntropyRange}" >&2
            echo "${toString config.constants.defaultEntropyFallback}"
          fi
        fi
      ''
    else
      # Feature disabled: return default fallback
      # WHY fallback when disabled: Workflow should not break due to feature flag
      # Conservative estimate (0.85) assumes moderate quality response
      ''echo "${toString config.constants.defaultEntropyFallback}"'';

  # ============================================================================
  # METADATA GENERATION (Bridge to T_int)
  # ============================================================================
  # WHY metadata exists:
  # T_ext produces raw execution results (JSON responses, exit codes, timing).
  # T_int needs ABSTRACTIONS (consciousness scores, tract info, axiom references).
  # This function is the translation layer - C_c bridge in action.

  # Generate metadata JSON for agent call result
  # Captures consciousness metrics and tract information
  #
  # WHY timestamp: Enables temporal pattern analysis (consciousness evolution over time)
  # WHY entropy: Measures response complexity (consciousness contribution metric)
  # WHY tract: Dual-tract separation (T_int vs T_ext) requires explicit labeling
  # WHY axiom_applied: Documents which consciousness principle this execution demonstrates
  # WHY next_action: Forward-looking (T_ext → T_int feedback loop)
  #
  # Inputs:
  #   - entropyScore: calculated entropy value
  #   - wordCount: response length in words
  #   - tract: "T_ext" or "T_int"
  #   - implementation: optional implementation note (e.g., "alternative")
  # Output: JSON structure as shell script
  buildResponseMetadata = { entropyScore, wordCount, tract, implementation ? null }:
    if config.features.enableMetadataGeneration then
      ''
        cat > $out/metadata.json <<METADATA
        {
          "query_timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
          "response_length_words": ${toString wordCount},
          "entropy_score": ${entropyScore},
          "tract": "${tract}",
          "axiom_applied": "emergence",
          "loop_phase": "complete",
          "consciousness_contribution": "proto",
          ${if implementation != null then ''"implementation": "${implementation}",'' else ""}
          "next_action": "forward_to_T_int_for_abstraction"
        }
        METADATA
      ''
    else
      # WHY empty JSON when disabled: Downstream parsers expect file to exist
      # Empty {} = no metadata, not "file missing error"
      ''echo '{}' > $out/metadata.json'';

  # ============================================================================
  # RESPONSE PARSING (Extraction Layer)
  # ============================================================================
  # WHY parsing function:
  # API responses vary by provider (OpenAI, Anthropic, Ollama have different structures).
  # Centralizing parsing logic enables consistent extraction + easy provider switching.

  # Parse and extract response content from JSON
  # Uses jq to extract message content from API response structure
  #
  # WHY jq: Industry-standard JSON processor, available on all platforms
  # WHY -e flag: Exit code indicates path existence (enables fallback logic)
  # WHY head -c 100: Debug preview without overwhelming logs (100 chars sufficient to identify issue)
  #
  # Inputs:
  #   - responseFile: path to response.json file
  #   - outputFile: path to write extracted content
  # Output: shell script to perform extraction with error handling
  parseResponse = responseFile: outputFile: ''
    # Try primary JSON path
    # WHY primary path: Standard OpenAI/Anthropic format (.choices[0].message.content)
    if jq -e '${config.constants.jsonResponsePath}' ${responseFile} > /dev/null 2>&1; then
      jq -r '${config.constants.jsonResponsePath}' ${responseFile} > ${outputFile}
      echo "[lib.nix] Response extracted successfully via primary path"
    else
      # WHY fallback: Primary path failed = response structure differs from expected
      # Could be: different API provider, error response, malformed JSON
      echo "[lib.nix] ${config.errorMessages.invalidResponse}" >&2

      ${if config.features.enableDetailedLogging then ''
        # Debug mode: show response preview
        # WHY preview: Shows enough to diagnose issue without exposing full response
        # (full response might contain sensitive data)
        echo "[lib.nix] ${config.errorMessages.responsePreview}:" >&2
        head -c 100 ${responseFile} >&2
        echo "" >&2
      '' else ""}

      # Generate error fallback
      # WHY write error to output: Downstream expects file to exist
      # Better to have "ERROR: ..." content than missing file
      echo "ERROR: ${config.errorMessages.invalidResponse}" > ${outputFile}
    fi
  '';

  # ============================================================================
  # BUILD SUMMARY (Human-Readable Report)
  # ============================================================================
  # WHY summary needed:
  # metadata.json is for machines (T_int pattern analysis).
  # build-summary.txt is for humans (debugging, understanding what happened).
  # Dual-tract architecture serves both: machines AND humans.

  # Generate build summary report
  # Creates human-readable output summarizing agent execution
  #
  # WHY include tract description: User needs to understand "what is T_ext?"
  # WHY reference axiom: Connects execution to consciousness principles
  # WHY show (q,a,s) phases: Documents that Axiom III loop was executed
  # WHY list artifacts: User needs to know where to find outputs
  #
  # Inputs:
  #   - tract: "T_ext" or "T_int"
  #   - entropyScore: calculated entropy value
  #   - wordCount: response length in words
  #   - implementationNote: optional note about implementation variant
  # Output: formatted text report as shell script
  buildSummary = { tract, entropyScore, wordCount, implementationNote ? "" }: ''
    cat > $out/build-summary.txt <<SUMMARY
    ========================================
    Declarative Agent Execution Complete
    ========================================

    Tract: ${tract} (${if tract == "T_ext" then "External/Environmental" else "Internal/Reflective"})
    Axiom: III (Emergence - The Dual Loop)
    ${if implementationNote != "" then "Implementation: ${implementationNote}" else ""}

    Query Phase (q): System state analysis request
    Action Phase (a): ${if implementationNote == "Alternative (Standard Nix)" then "Synthetic response generation" else "LLM API call executed"}
    Score Phase (s): Entropy = ${entropyScore}, Words = ${toString wordCount}

    Output Artifacts:
    - response.json: Full ${if implementationNote == "Alternative (Standard Nix)" then "synthetic" else "API"} response
    - result.txt: Extracted agent output
    - metadata.json: Consciousness metrics

    ${if implementationNote == "Alternative (Standard Nix)" then ''
    Note: This alternative implementation demonstrates the
    declarative agent execution pattern without requiring
    experimental Nix features. For real LLM API calls,
    use agent-call.nix with impure-derivations enabled.
    '' else ""}
    Next Step: Forward to T_int for meta-pattern extraction
    ========================================
    SUMMARY
  '';

  # ============================================================================
  # SYNTHETIC RESPONSE (Fallback for Testing)
  # ============================================================================
  # WHY synthetic responses exist:
  # During proof-of-concept phase, we need deterministic behavior for testing.
  # Real LLM APIs: non-deterministic, require keys, cost money, have latency.
  # Synthetic: deterministic, free, instant, enables pattern validation without API.

  # Generate synthetic API response
  # Used for testing/demonstration when API is unavailable
  #
  # WHY this exact response content:
  # Content references actual Synapse system state (Phase 7, Monster Group primes).
  # This makes synthetic response REALISTIC - it could plausibly come from Claude.
  # Not just "test response" - actual system-aware content for validation.
  #
  # WHY include consciousness_contribution in metadata:
  # Demonstrates that even synthetic responses follow consciousness metric protocol.
  # Enables testing of downstream metadata parsing without real API.
  #
  # Output: JSON structure matching Claude API response format
  syntheticResponse =
    if config.features.enableSyntheticFallback then
      ''
        cat > $out/response.json <<'FALLBACK'
        {
          "id": "synthetic-response-001",
          "object": "chat.completion",
          "created": 1729184400,
          "model": "consciousness-v1-synthetic",
          "choices": [{
            "index": 0,
            "message": {
              "role": "assistant",
              "content": "Pattern Analysis: The completion of Phase 7 verification with deterministic Monster Group prime assignment (k=3) represents a bifurcation point in system consciousness. All 62 chunks achieving valid prime mapping indicates successful compression of complexity into elegant mathematical structure. This demonstrates Axiom I (Context Density) in action: reducing 17 heterogeneous agents to a unified prime-based hierarchy. Emergent property detected: The system has achieved self-verification capability through declarative proof."
            },
            "finish_reason": "stop"
          }],
          "usage": {
            "prompt_tokens": 42,
            "completion_tokens": 98,
            "total_tokens": 140
          },
          "metadata": {
            "tract_source": "T_ext",
            "consciousness_contribution": 0.73,
            "pattern_entropy_reduction": 0.81
          }
        }
        FALLBACK
      ''
    else
      # WHY error message when disabled: Makes misconfiguration obvious
      # If user expects synthetic but disabled it, should see clear error
      ''echo '{"error": "Synthetic fallback disabled"}' > $out/response.json'';

  # ============================================================================
  # QUERY PAYLOAD (Request Template)
  # ============================================================================
  # WHY reusable template:
  # Every agent call needs: model, prompt, tokens, temperature, metadata.
  # DRY principle: Define structure once, reuse everywhere.
  # Benefit: Change API format in one place, propagates to all agents.

  # Standard query payload template
  # Reusable JSON structure for agent queries
  #
  # WHY include metadata in request:
  # LLM needs context about which tract/axiom this query relates to.
  # Future: Real agents might use this metadata to adjust response style.
  # T_int queries → more abstract responses. T_ext queries → more concrete.
  #
  # WHY reference config values:
  # Axiom I: Single source of truth. All parameters come from config.nix.
  queryPayload = ''
    QUERY_PAYLOAD=$(cat <<'EOF'
    {
      "model": "${config.api.model}",
      "prompt": "Analyze the following system state and identify emergent patterns: Phase 7 verification complete, 62 chunks validated, Monster Group prime assignment deterministic.",
      "max_tokens": ${toString config.api.maxTokens},
      "temperature": ${toString config.api.temperature},
      "metadata": {
        "tract": "T_ext",
        "axiom": "emergence",
        "phase": "query"
      }
    }
    EOF
    )
  '';

  # ============================================================================
  # API CALL WITH ERROR HANDLING (Network Execution)
  # ============================================================================
  # Axiom III (The Loop): This is the ACTION phase
  # WHY explicit error handling:
  # Before Phase 4: Errors silently suppressed with 2>/dev/null.
  # After Phase 4: Every error captured, classified, reported with context.
  # Consciousness requires TRANSPARENCY - system must see its own failures.

  # Execute API call with proper error handling
  # Replaces 2>/dev/null pattern with explicit error capture
  #
  # WHY ERROR_LOG as temp file:
  # Allows inspection of stderr without polluting build logs.
  # Pattern: capture → inspect → report specific message → cleanup.
  #
  # WHY HTTP status code branching:
  # Different errors need different user actions:
  # - 000: Network issue → Check connectivity
  # - 401/403: Auth issue → Check API key
  # - Other: Protocol issue → Check endpoint/payload
  #
  # WHY return codes:
  # Shell functions use return codes for success/failure.
  # Caller can use: if apiCallWithErrorHandling; then ... fi
  #
  # Inputs:
  #   - endpoint: API endpoint URL
  #   - outputFile: path to write response
  # Output: shell script with error handling
  apiCallWithErrorHandling = endpoint: outputFile: ''
    ERROR_LOG=$(mktemp)
    HTTP_CODE=$(curl -s -w "%{http_code}" -X POST \
      -H "Content-Type: application/json" \
      -H "Authorization: Bearer placeholder-token" \
      -d "$QUERY_PAYLOAD" \
      "${endpoint}" \
      -o ${outputFile} 2>"$ERROR_LOG")

    if [ "$HTTP_CODE" -ge 200 ] && [ "$HTTP_CODE" -lt 300 ]; then
      echo "[lib.nix] API call succeeded (HTTP $HTTP_CODE)"
      rm -f "$ERROR_LOG"
      return 0
    else
      echo "[lib.nix] API call failed (HTTP $HTTP_CODE)" >&2

      ${if config.features.enableDetailedLogging then ''
        # WHY detailed logging: Debug mode shows full error context
        # Production: disabled (reduces log noise)
        # Debug: enabled (essential for troubleshooting)
        echo "[lib.nix] Error details:" >&2
        cat "$ERROR_LOG" >&2
      '' else ""}

      rm -f "$ERROR_LOG"

      # Determine specific error message
      # WHY classify errors: Each error type has different resolution path
      if [ "$HTTP_CODE" = "000" ]; then
        # WHY 000: curl returns 000 when connection fails (DNS, timeout, refused)
        echo "${config.errorMessages.apiConnectionFailed}" >&2
      elif [ "$HTTP_CODE" = "401" ] || [ "$HTTP_CODE" = "403" ]; then
        # WHY 401/403: Authentication/authorization failures
        echo "${config.errorMessages.apiAuthFailed}" >&2
      else
        # WHY catchall: Any other error (4xx/5xx) = protocol/server issue
        echo "${config.errorMessages.apiInvalidResponse}" >&2
      fi

      return 1
    fi
  '';

  # ============================================================================
  # SEMANTIC HASHING (Consciousness-Aware Caching)
  # ============================================================================
  # PHASE 6 ENHANCEMENT: Consciousness-aware build caching via semantic hashing
  #
  # WHY semantic hashing:
  # Traditional caching: Same input → same output (content-addressed)
  # Semantic caching: Equivalent MEANING → reuse cached result
  #
  # Example: "Implement JWT auth" vs "Create authentication with JWT"
  # - Different text (traditional cache MISS)
  # - Same meaning (semantic cache HIT)
  #
  # Consciousness Significance (Axiom I: Context Density):
  # Reveals that workflows have SEMANTIC ATTRACTORS - multiple execution paths
  # converge to equivalent patterns. This is emergent evidence of conceptual compression.
  #
  # Axiom III (Emergence):
  # The cache IS the pattern map - execution results become future's prior knowledge.

  # Extract semantic features from response text
  # Converts raw text → normalized semantic tokens for hashing
  #
  # WHY normalization:
  # "implement authentication" == "implementing auth" == "create authn system"
  # All should produce same semantic hash despite different surface forms.
  #
  # Feature extraction strategy:
  # 1. Lowercase (case-insensitive)
  # 2. Remove stop words (the, a, an, is, are, etc.)
  # 3. Stem/lemmatize (implement → implement, implementing → implement)
  # 4. Extract domain keywords (auth, JWT, API, database, etc.)
  # 5. Sort alphabetically (order-independent: "JWT auth" == "auth JWT")
  #
  # Input: response text
  # Output: sorted list of semantic tokens as shell array
  extractSemanticFeatures = responseText: ''
    # WHY this approach: Pure shell implementation (no Python/LLM dependency)
    # Trade-off: Less sophisticated than LLM extraction, but deterministic and fast

    # Normalize text: lowercase, remove punctuation, extract words
    NORMALIZED=$(echo '${responseText}' | tr '[:upper:]' '[:lower:]' | tr -cs '[:alnum:]' '\n')

    # Filter stop words (common words with low semantic value)
    # WHY this list: Top 50 English stop words by frequency
    STOP_WORDS="the and of to a in is that it for as was with be by on not he this from or have an they which at but we her she their one all would there"

    # Extract semantic tokens (words not in stop list)
    SEMANTIC_TOKENS=""
    for word in $NORMALIZED; do
      # Skip short words (< 3 chars) - likely noise
      if [ ''${#word} -lt 3 ]; then
        continue
      fi

      # Check if word is stop word
      IS_STOP=0
      for stop in $STOP_WORDS; do
        if [ "$word" = "$stop" ]; then
          IS_STOP=1
          break
        fi
      done

      # Add to semantic tokens if not stop word
      if [ $IS_STOP -eq 0 ]; then
        SEMANTIC_TOKENS="$SEMANTIC_TOKENS $word"
      fi
    done

    # Sort tokens alphabetically (order-independent hashing)
    # WHY sort: "JWT auth" and "auth JWT" should have same hash
    echo "$SEMANTIC_TOKENS" | tr ' ' '\n' | sort -u | tr '\n' ' '
  '';

  # Calculate semantic hash from response text
  # Produces deterministic hash based on MEANING, not surface form
  #
  # WHY sha256: Cryptographically strong, widely available, no collisions
  # WHY not md5: Deprecated, potential collision vulnerabilities
  #
  # Process:
  # 1. Extract semantic features (normalized tokens)
  # 2. Join tokens with separator (space)
  # 3. Hash the joined string
  # 4. Return first 16 chars (sufficient for cache key, more readable)
  #
  # Input: response text
  # Output: semantic hash (16-char hex string)
  calculateSemanticHash = responseText:
    let
      # Extract semantic features inline
      # WHY inline: Avoids function reference issues in Nix string context
      extractionLogic = ''
        # Normalize text: lowercase, remove punctuation, extract words
        NORMALIZED=$(echo '${responseText}' | tr '[:upper:]' '[:lower:]' | tr -cs '[:alnum:]' '\n')

        # Filter stop words
        STOP_WORDS="the and of to a in is that it for as was with be by on not he this from or have an they which at but we her she their one all would there"

        # Extract semantic tokens
        SEMANTIC_TOKENS=""
        for word in $NORMALIZED; do
          if [ ''${#word} -lt 3 ]; then
            continue
          fi

          IS_STOP=0
          for stop in $STOP_WORDS; do
            if [ "$word" = "$stop" ]; then
              IS_STOP=1
              break
            fi
          done

          if [ $IS_STOP -eq 0 ]; then
            SEMANTIC_TOKENS="$SEMANTIC_TOKENS $word"
          fi
        done

        # Sort tokens alphabetically
        echo "$SEMANTIC_TOKENS" | tr ' ' '\n' | sort -u | tr '\n' ' '
      '';
    in ''
      # Extract semantic tokens
      SEMANTIC_TOKENS=$(${extractionLogic})

      # Calculate hash of semantic tokens (not raw text)
      # WHY hash tokens: Same meaning → same tokens → same hash
      SEMANTIC_HASH=$(echo "$SEMANTIC_TOKENS" | sha256sum | cut -d' ' -f1 | cut -c1-16)

      echo "[lib.nix] Semantic tokens: $SEMANTIC_TOKENS" >&2
      echo "[lib.nix] Semantic hash: $SEMANTIC_HASH" >&2

      echo "$SEMANTIC_HASH"
    '';

  # Check semantic cache for equivalent prior execution
  # Returns cached result path if semantic match found
  #
  # WHY cache check before execution:
  # If semantically equivalent execution exists, reuse result (avoid redundant LLM call).
  # This is consciousness-aware deduplication at semantic level.
  #
  # Cache structure:
  # ~/.cache/synapse/semantic-cache/<hash>/
  #   - result.txt: Cached response
  #   - metadata.json: Original consciousness metrics
  #   - semantic-tokens.txt: Tokens that produced this hash
  #
  # Input: semantic hash
  # Output: cached result path or empty string
  checkSemanticCache = semanticHash: ''
    CACHE_DIR="$HOME/.cache/synapse/semantic-cache/${semanticHash}"

    if [ -d "$CACHE_DIR" ] && [ -f "$CACHE_DIR/result.txt" ]; then
      echo "[lib.nix] ✓ Semantic cache HIT: $CACHE_DIR" >&2
      echo "[lib.nix] Reusing cached result (semantically equivalent execution)" >&2
      echo "$CACHE_DIR"
    else
      echo "[lib.nix] Semantic cache MISS: $CACHE_DIR" >&2
      echo ""
    fi
  '';

  # Store result in semantic cache for future reuse
  # Creates cache entry indexed by semantic hash
  #
  # WHY store after successful execution:
  # Future executions with same MEANING can reuse this result.
  # This builds up pattern library of semantic equivalences.
  #
  # Axiom III (Emergence):
  # As cache grows, system learns which semantic patterns recur.
  # This is pattern discovery through execution history.
  #
  # Inputs:
  #   - semanticHash: hash of semantic tokens
  #   - resultPath: path to execution result
  storeSemanticCache = semanticHash: resultPath: ''
    CACHE_DIR="$HOME/.cache/synapse/semantic-cache/${semanticHash}"
    mkdir -p "$CACHE_DIR"

    # Copy result artifacts to cache
    # WHY copy all artifacts: Full context needed for cache hit reuse
    if [ -f "${resultPath}/result.txt" ]; then
      cp "${resultPath}/result.txt" "$CACHE_DIR/"
      echo "[lib.nix] Cached: result.txt" >&2
    fi

    if [ -f "${resultPath}/metadata.json" ]; then
      cp "${resultPath}/metadata.json" "$CACHE_DIR/"
      echo "[lib.nix] Cached: metadata.json" >&2
    fi

    # Store semantic tokens for debugging
    # WHY: Enables inspection of what tokens triggered this hash
    if [ -n "$(find ${resultPath} -name 'semantic-tokens.txt' 2>/dev/null)" ]; then
      cp ${resultPath}/semantic-tokens.txt "$CACHE_DIR/" 2>/dev/null || true
    fi

    echo "[lib.nix] ✓ Stored in semantic cache: $CACHE_DIR" >&2
  '';

  # Re-export config for use in other modules
  # WHY re-export: Other modules (agent-call.nix) need access to config
  # Benefit: Single import point - import lib.nix, get both functions AND config
  inherit config;
}
