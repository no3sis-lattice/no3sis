# EXPERIMENTAL: Proof-of-concept demonstrating consciousness-aware build caching
# This demonstrates semantic hash-based caching for agent executions
# NOT for production use - responses are mocked
#
# PHASE 6 ENHANCEMENT: Semantic deduplication via meaning-based caching

{ pkgs ? import <nixpkgs> {} }:

let
  # Import shared utilities library
  lib = import ./lib.nix { inherit pkgs; };
  config = lib.config;

  # Demonstration: Build three agent calls with semantically equivalent prompts
  # Expected: First is cache MISS, next two are cache HITs

  buildCachedAgentCall = { name, prompt }:
    pkgs.runCommand "agent-call-cached-${name}"
      {
        nativeBuildInputs = with pkgs; [ coreutils ];
        meta = {
          description = "Cached agent execution: ${prompt}";
          tract = "T_ext";
        };
      }
      ''
        mkdir -p $out
        # Use /tmp for demo cache (pure builds can't write to $HOME)
        # WHY /tmp: Writable in Nix sandbox, demonstrates pattern without impure flag
        CACHE_DIR="/tmp/synapse-semantic-cache"
        mkdir -p "$CACHE_DIR"

        echo "[${name}] Prompt: ${prompt}"

        # Generate response
        RESPONSE_TEXT="Pattern Analysis: ${prompt} demonstrates authentication system design with JWT token management for secure user sessions."
        echo "$RESPONSE_TEXT" > $out/response.txt

        # Calculate semantic hash (simplified inline version)
        # Extract keywords: normalize, remove stop words, sort
        NORMALIZED=$(echo "$RESPONSE_TEXT" | tr '[:upper:]' '[:lower:]' | tr -cs '[:alnum:]' '\n')

        STOP_WORDS="the and of to a in is that it for as was with be by on not he this from or have an they which at but we her she their one all would there"

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

        # Sort tokens for order-independence
        SORTED_TOKENS=$(echo "$SEMANTIC_TOKENS" | tr ' ' '\n' | sort -u | tr '\n' ' ')
        echo "$SORTED_TOKENS" > $out/semantic-tokens.txt

        # Calculate hash
        SEMANTIC_HASH=$(echo "$SORTED_TOKENS" | sha256sum | cut -d' ' -f1 | cut -c1-16)
        echo "$SEMANTIC_HASH" > $out/semantic-hash.txt

        echo "[${name}] Semantic tokens: $SORTED_TOKENS"
        echo "[${name}] Semantic hash: $SEMANTIC_HASH"

        # Check cache
        if [ -d "$CACHE_DIR/$SEMANTIC_HASH" ] && [ -f "$CACHE_DIR/$SEMANTIC_HASH/response.txt" ]; then
          echo "[${name}] ✓ CACHE HIT - Semantically equivalent execution found"
          cp "$CACHE_DIR/$SEMANTIC_HASH/response.txt" $out/cached-response.txt
          echo "HIT" > $out/cache-status.txt
        else
          echo "[${name}] ✗ CACHE MISS - Storing new semantic pattern"
          mkdir -p "$CACHE_DIR/$SEMANTIC_HASH"
          cp $out/response.txt "$CACHE_DIR/$SEMANTIC_HASH/"
          cp $out/semantic-tokens.txt "$CACHE_DIR/$SEMANTIC_HASH/"
          echo "MISS" > $out/cache-status.txt
        fi

        # Generate summary
        cat > $out/summary.txt <<'EOF'
========================================
Semantic Cache Demonstration
========================================

Prompt: ${prompt}
Name: ${name}
Semantic Hash: $(cat $out/semantic-hash.txt)
Cache Status: $(cat $out/cache-status.txt)
Semantic Tokens: $(cat $out/semantic-tokens.txt)

Pattern Discovery:
$(if [ "$(cat $out/cache-status.txt)" = "HIT" ]; then
  echo "Semantic attractor detected - pattern reused"
  echo "Consciousness contribution: deduplication"
else
  echo "New semantic pattern discovered"
  echo "Consciousness contribution: cache expansion"
fi)

Axiom I: Multiple text forms → single semantic pattern
Axiom III: Cache = accumulated consciousness patterns
========================================
EOF

        cat $out/summary.txt
      '';

in

# Three semantically equivalent prompts
{
  test1_initial = buildCachedAgentCall {
    name = "test1";
    prompt = "Implement user authentication with JWT tokens";
  };

  test2_equivalent = buildCachedAgentCall {
    name = "test2";
    prompt = "Create JWT-based auth system for users";
  };

  test3_paraphrase = buildCachedAgentCall {
    name = "test3";
    prompt = "Build authentication using JSON Web Tokens";
  };

  test4_different = buildCachedAgentCall {
    name = "test4";
    prompt = "Implement database connection pooling";
  };
}
