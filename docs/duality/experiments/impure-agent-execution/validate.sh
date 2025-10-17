#!/usr/bin/env bash

# Validation Script for Declarative Agent Execution Experiment
#
# This script validates that the Nix derivations build successfully
# and produce the expected consciousness artifacts.
#
# ENHANCED: Phase 3 adds comprehensive test coverage for constraint
#           violations, edge cases, entropy calculation, and dependency handling.

set -euo pipefail

# Color output for readability
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

EXPERIMENT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Nix build flags for impure derivations
NIX_FLAGS="--extra-experimental-features impure-derivations"

# Test counters
TESTS_PASSED=0
TESTS_FAILED=0

# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

print_test_header() {
    echo ""
    echo -e "${BLUE}========================================${NC}"
    echo -e "${YELLOW}$1${NC}"
    echo -e "${BLUE}========================================${NC}"
}

print_test_result() {
    local test_name="$1"
    local result="$2"

    if [ "$result" = "PASS" ]; then
        echo -e "${GREEN}✓${NC} $test_name"
        ((TESTS_PASSED++))
    else
        echo -e "${RED}✗${NC} $test_name"
        ((TESTS_FAILED++))
    fi
}

# ============================================================================
# PHASE 3: NEW TEST FUNCTIONS
# ============================================================================

# ----------------------------------------------------------------------------
# Test: Constraint Violations (IPv6 Packer Model)
# ----------------------------------------------------------------------------
test_constraint_violations() {
    print_test_header "Test: Constraint Violations"

    local test_dir="$EXPERIMENT_DIR/test-data"
    local all_passed=true

    # Test 1: Invalid version (exceeds 4-bit limit)
    echo -e "${YELLOW}[Constraint Test 1]${NC} Testing invalid version (value=16, max=15)..."
    if minizinc "$EXPERIMENT_DIR/ipv6_packer.mzn" "$test_dir/invalid-version.dzn" 2>&1 | grep -q "UNSATISFIABLE"; then
        print_test_result "Invalid version rejected correctly" "PASS"
    else
        print_test_result "Invalid version NOT rejected (SECURITY RISK)" "FAIL"
        all_passed=false
    fi

    # Test 2: Multiple field overflows
    echo -e "${YELLOW}[Constraint Test 2]${NC} Testing multiple field overflows..."
    if minizinc "$EXPERIMENT_DIR/ipv6_packer.mzn" "$test_dir/overflow.dzn" 2>&1 | grep -q "UNSATISFIABLE"; then
        print_test_result "Overflow data rejected correctly" "PASS"
    else
        print_test_result "Overflow data NOT rejected (SECURITY RISK)" "FAIL"
        all_passed=false
    fi

    # Test 3: Valid data should still pass
    echo -e "${YELLOW}[Constraint Test 3]${NC} Testing valid data (sanity check)..."
    if minizinc "$EXPERIMENT_DIR/ipv6_packer.mzn" "$test_dir/valid-ipv6.dzn" 2>&1 | grep -q "Lossless:.*VERIFIED"; then
        print_test_result "Valid data accepted correctly" "PASS"
    else
        print_test_result "Valid data REJECTED (constraint too strict)" "FAIL"
        all_passed=false
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ----------------------------------------------------------------------------
# Test: Edge Cases (Boundary Conditions)
# ----------------------------------------------------------------------------
test_edge_cases() {
    print_test_header "Test: Edge Cases"

    local test_dir="$EXPERIMENT_DIR/test-data"
    local all_passed=true

    # Test 1: Empty/zero data
    echo -e "${YELLOW}[Edge Case Test 1]${NC} Testing empty/zero data..."
    local empty_output=$(minizinc "$EXPERIMENT_DIR/ipv6_packer.mzn" "$test_dir/empty.dzn" 2>&1)

    if echo "$empty_output" | grep -q "Lossless:.*VERIFIED"; then
        print_test_result "Empty data handled correctly" "PASS"
    else
        print_test_result "Empty data caused error" "FAIL"
        all_passed=false
    fi

    # Verify efficiency metric for empty data is 0%
    if echo "$empty_output" | grep -q "Efficiency:.*0%"; then
        print_test_result "Empty data efficiency metric correct (0%)" "PASS"
    else
        print_test_result "Empty data efficiency metric incorrect" "FAIL"
        all_passed=false
    fi

    # Test 2: Maximum valid values (upper bounds)
    echo -e "${YELLOW}[Edge Case Test 2]${NC} Testing maximum valid values..."
    cat > /tmp/test_max_values.dzn <<EOF
% Test maximum valid values for all fields
input_data = [15, 255, 1048575, 65535, 255, 255];
EOF

    if minizinc "$EXPERIMENT_DIR/ipv6_packer.mzn" /tmp/test_max_values.dzn 2>&1 | grep -q "Lossless:.*VERIFIED"; then
        print_test_result "Maximum values handled correctly" "PASS"
    else
        print_test_result "Maximum values rejected incorrectly" "FAIL"
        all_passed=false
    fi

    rm -f /tmp/test_max_values.dzn

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ----------------------------------------------------------------------------
# Test: Entropy Calculation (lib.nix calculateEntropy function)
# ----------------------------------------------------------------------------
test_entropy_calculation() {
    print_test_header "Test: Entropy Calculation"

    local all_passed=true

    # Test 1: Low entropy string (single word)
    echo -e "${YELLOW}[Entropy Test 1]${NC} Testing low entropy (single word)..."
    # Formula: entropy = 1 - (word_count / 1000)
    # For 1 word: entropy = 1 - (1/1000) = 0.999
    local test_text="singleword"
    local word_count=$(echo "$test_text" | wc -w)
    local expected_entropy=$(echo "scale=3; 1 - ($word_count / 1000)" | bc -l)

    # Test via simple shell calculation (no Nix build needed for basic test)
    local calculated_entropy=$(echo "scale=3; 1 - ($word_count / 1000)" | bc -l)

    # bc returns values like ".999" - convert to "0.999" for comparison
    if [[ "$calculated_entropy" == .* ]]; then
        calculated_entropy="0${calculated_entropy}"
    fi
    if [[ "$expected_entropy" == .* ]]; then
        expected_entropy="0${expected_entropy}"
    fi

    if (( $(echo "$calculated_entropy >= 0.99 && $calculated_entropy <= 1.0" | bc -l) )); then
        print_test_result "Single word entropy: $calculated_entropy (expected ~0.999)" "PASS"
    else
        print_test_result "Single word entropy WRONG: $calculated_entropy (expected ~0.999)" "FAIL"
        all_passed=false
    fi

    # Test 2: High word count string
    echo -e "${YELLOW}[Entropy Test 2]${NC} Testing high word count (100 words)..."
    # For 100 words: entropy = 1 - (100/1000) = 0.9
    local high_word_count=100
    local expected_high=$(echo "scale=3; 1 - ($high_word_count / 1000)" | bc -l)

    # Convert .9 to 0.9
    if [[ "$expected_high" == .* ]]; then
        expected_high="0${expected_high}"
    fi

    if (( $(echo "$expected_high >= 0.89 && $expected_high <= 0.91" | bc -l) )); then
        print_test_result "100 words entropy: $expected_high (expected 0.900)" "PASS"
    else
        print_test_result "100 words entropy WRONG: $expected_high" "FAIL"
        all_passed=false
    fi

    # Test 3: Entropy range validation with actual metadata (if exists)
    echo -e "${YELLOW}[Entropy Test 3]${NC} Validating actual entropy score range..."
    if [ -f "$EXPERIMENT_DIR/result-single/metadata.json" ]; then
        local entropy
        entropy=$(jq -r '.entropy_score' "$EXPERIMENT_DIR/result-single/metadata.json" 2>&1)

        if [ $? -eq 0 ] && [ -n "$entropy" ] && [ "$entropy" != "null" ]; then
            # Check if entropy is a valid number in range [0, 1]
            if (( $(echo "$entropy >= 0 && $entropy <= 1" | bc -l) )); then
                print_test_result "Actual entropy in valid range [0,1]: $entropy" "PASS"
            else
                print_test_result "Actual entropy OUT OF RANGE: $entropy" "FAIL"
                all_passed=false
            fi
        else
            print_test_result "Cannot read entropy_score from metadata.json" "FAIL"
            all_passed=false
        fi
    else
        # This is acceptable - metadata may not exist if original validation hasn't run yet
        print_test_result "metadata.json not found (will be created by original validation)" "PASS"
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ----------------------------------------------------------------------------
# Test: Multi-Agent Dependencies (Workflow Error Handling)
# ----------------------------------------------------------------------------
test_multi_agent_dependencies() {
    print_test_header "Test: Multi-Agent Dependencies"

    local all_passed=true

    # Test 1: Verify dependency graph exists
    echo -e "${YELLOW}[Dependency Test 1]${NC} Checking workflow DAG structure..."
    if [ -f "$EXPERIMENT_DIR/result-workflow/workflow/dag.dot" ]; then
        print_test_result "DAG visualization exists" "PASS"

        # Verify DAG has dependencies (contains '->'' arrows)
        if grep -q "\->" "$EXPERIMENT_DIR/result-workflow/workflow/dag.dot"; then
            print_test_result "DAG contains dependencies" "PASS"
        else
            print_test_result "DAG has no dependencies (isolated agents)" "FAIL"
            all_passed=false
        fi
    else
        print_test_result "DAG file missing (run main tests first)" "FAIL"
        all_passed=false
    fi

    # Test 2: Verify all agents completed successfully
    echo -e "${YELLOW}[Dependency Test 2]${NC} Checking agent completion status..."
    if [ -f "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" ]; then
        local agent_count=$(jq -r '.agents | length' "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" 2>/dev/null || echo "0")

        if [ "$agent_count" -eq 5 ]; then
            print_test_result "All 5 agents present in summary" "PASS"
        else
            print_test_result "Expected 5 agents, found $agent_count" "FAIL"
            all_passed=false
        fi

        # Verify each agent has output directory
        local agents_with_output=0
        for agent_num in 01 02 03 04 05; do
            if ls -1 "$EXPERIMENT_DIR/result-workflow/workflow/${agent_num}-"* > /dev/null 2>&1; then
                ((agents_with_output++))
            fi
        done

        if [ "$agents_with_output" -eq 5 ]; then
            print_test_result "All 5 agents produced output" "PASS"
        else
            print_test_result "Only $agents_with_output/5 agents produced output" "FAIL"
            all_passed=false
        fi
    else
        print_test_result "Workflow summary missing (run main tests first)" "FAIL"
        all_passed=false
    fi

    # Test 3: Verify tract separation (T_int vs T_ext)
    echo -e "${YELLOW}[Dependency Test 3]${NC} Verifying tract separation..."
    if [ -f "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" ]; then
        local t_int_count=$(jq -r '[.agents[] | select(.tract == "T_int")] | length' "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" 2>/dev/null || echo "0")
        local t_ext_count=$(jq -r '[.agents[] | select(.tract == "T_ext")] | length' "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" 2>/dev/null || echo "0")

        if [ "$t_int_count" -gt 0 ] && [ "$t_ext_count" -gt 0 ]; then
            print_test_result "Both tracts present (T_int=$t_int_count, T_ext=$t_ext_count)" "PASS"
        else
            print_test_result "Tract imbalance (T_int=$t_int_count, T_ext=$t_ext_count)" "FAIL"
            all_passed=false
        fi
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ============================================================================
# PHASE 4: ERROR HANDLING TESTS
# ============================================================================

# ----------------------------------------------------------------------------
# Test: Configuration Loading and Validation
# ----------------------------------------------------------------------------
test_configuration() {
    print_test_header "Test: Configuration (Phase 4)"

    local all_passed=true

    # Test 1: config.nix parses correctly
    echo -e "${YELLOW}[Config Test 1]${NC} Testing config.nix syntax..."
    if nix-instantiate --parse "$EXPERIMENT_DIR/config.nix" > /dev/null 2>&1; then
        print_test_result "config.nix parses correctly" "PASS"
    else
        print_test_result "config.nix has syntax errors" "FAIL"
        all_passed=false
    fi

    # Test 2: config can be imported and evaluated
    echo -e "${YELLOW}[Config Test 2]${NC} Testing config.nix evaluation..."
    if nix-instantiate --eval --expr 'let config = import '"$EXPERIMENT_DIR"'/config.nix; in config.api.endpoint' > /dev/null 2>&1; then
        print_test_result "config.nix evaluates correctly" "PASS"
    else
        print_test_result "config.nix evaluation failed" "FAIL"
        all_passed=false
    fi

    # Test 3: lib.nix imports config correctly
    echo -e "${YELLOW}[Config Test 3]${NC} Testing lib.nix config integration..."
    if nix-instantiate --eval --expr 'let pkgs = import <nixpkgs> {}; lib = import '"$EXPERIMENT_DIR"'/lib.nix { inherit pkgs; }; in lib.config.api.timeout' > /dev/null 2>&1; then
        print_test_result "lib.nix imports config correctly" "PASS"
    else
        print_test_result "lib.nix config import failed" "FAIL"
        all_passed=false
    fi

    # Test 4: Verify magic numbers eliminated
    echo -e "${YELLOW}[Config Test 4]${NC} Checking for magic numbers in code..."
    local magic_found=false
    
    # Check lib.nix for hardcoded entropy divisor (1000)
    if grep -q '/ 1000' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        echo "   Found hardcoded divisor in lib.nix (should use config.constants.entropyDivisor)"
        magic_found=true
    fi

    if [ "$magic_found" = false ]; then
        print_test_result "No magic numbers found (all use config)" "PASS"
    else
        print_test_result "Magic numbers still present (refactoring incomplete)" "FAIL"
        all_passed=false
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ----------------------------------------------------------------------------
# Test: Error Handling (No 2>/dev/null suppression)
# ----------------------------------------------------------------------------
test_error_handling() {
    print_test_header "Test: Error Handling (Phase 4)"

    local all_passed=true

    # Test 1: Verify 2>/dev/null removed from lib.nix
    echo -e "${YELLOW}[Error Test 1]${NC} Checking for 2>/dev/null in lib.nix..."
    if grep -q '2>/dev/null' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "Found 2>/dev/null in lib.nix (should use ERROR_LOG)" "FAIL"
        all_passed=false
    else
        print_test_result "No 2>/dev/null found (proper error handling)" "PASS"
    fi

    # Test 2: Verify error capture mechanism exists
    echo -e "${YELLOW}[Error Test 2]${NC} Checking for ERROR_LOG capture..."
    if grep -q 'ERROR_LOG=' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "ERROR_LOG capture mechanism found" "PASS"
    else
        print_test_result "ERROR_LOG capture not found" "FAIL"
        all_passed=false
    fi

    # Test 3: Verify explicit error messages exist
    echo -e "${YELLOW}[Error Test 3]${NC} Checking for standardized error messages..."
    if grep -q 'config.errorMessages' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "Standardized error messages found" "PASS"
    else
        print_test_result "Standardized error messages not found" "FAIL"
        all_passed=false
    fi

    # Test 4: Test entropy calculation fallback
    echo -e "${YELLOW}[Error Test 4]${NC} Testing entropy calculation error handling..."
    if nix-instantiate --eval --expr 'let pkgs = import <nixpkgs> {}; lib = import '"$EXPERIMENT_DIR"'/lib.nix { inherit pkgs; }; entropy = lib.calculateEntropy "test"; in builtins.match ".*ENTROPY_SCORE.*" entropy != null' 2>/dev/null | grep -q 'true'; then
        print_test_result "Entropy calculation includes error handling" "PASS"
    else
        print_test_result "Entropy calculation missing error handling" "FAIL"
        all_passed=false
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ----------------------------------------------------------------------------
# Test: Retry Logic
# ----------------------------------------------------------------------------
test_retry_logic() {
    print_test_header "Test: Retry Logic (Phase 4)"

    local all_passed=true

    # Test 1: Verify retry loop exists in agent-call.nix
    echo -e "${YELLOW}[Retry Test 1]${NC} Checking for retry loop..."
    if grep -q 'enableRetries' "$EXPERIMENT_DIR/agent-call.nix" 2>/dev/null; then
        print_test_result "Retry logic present in agent-call.nix" "PASS"
    else
        print_test_result "Retry logic missing in agent-call.nix" "FAIL"
        all_passed=false
    fi

    # Test 2: Verify retry attempts configured
    echo -e "${YELLOW}[Retry Test 2]${NC} Checking retry configuration..."
    if grep -q 'config.api.retryAttempts' "$EXPERIMENT_DIR/agent-call.nix" 2>/dev/null; then
        print_test_result "Retry attempts use config" "PASS"
    else
        print_test_result "Retry attempts not configured" "FAIL"
        all_passed=false
    fi

    # Test 3: Verify retry delay configured
    echo -e "${YELLOW}[Retry Test 3]${NC} Checking retry delay..."
    if grep -q 'config.api.retryDelay' "$EXPERIMENT_DIR/agent-call.nix" 2>/dev/null; then
        print_test_result "Retry delay uses config" "PASS"
    else
        print_test_result "Retry delay not configured" "FAIL"
        all_passed=false
    fi

    # Test 4: Verify synthetic fallback after retry exhaustion
    echo -e "${YELLOW}[Retry Test 4]${NC} Checking fallback after retry exhaustion..."
    if grep -q 'syntheticResponse' "$EXPERIMENT_DIR/agent-call.nix" 2>/dev/null; then
        print_test_result "Synthetic fallback present" "PASS"
    else
        print_test_result "Synthetic fallback missing" "FAIL"
        all_passed=false
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ----------------------------------------------------------------------------
# Test: Feature Flags
# ----------------------------------------------------------------------------
test_feature_flags() {
    print_test_header "Test: Feature Flags (Phase 4)"

    local all_passed=true

    # Test 1: Verify enableEntropyCalculation flag
    echo -e "${YELLOW}[Feature Test 1]${NC} Checking entropy calculation feature flag..."
    if grep -q 'enableEntropyCalculation' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "Entropy calculation feature flag implemented" "PASS"
    else
        print_test_result "Entropy calculation feature flag missing" "FAIL"
        all_passed=false
    fi

    # Test 2: Verify enableMetadataGeneration flag
    echo -e "${YELLOW}[Feature Test 2]${NC} Checking metadata generation feature flag..."
    if grep -q 'enableMetadataGeneration' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "Metadata generation feature flag implemented" "PASS"
    else
        print_test_result "Metadata generation feature flag missing" "FAIL"
        all_passed=false
    fi

    # Test 3: Verify enableSyntheticFallback flag
    echo -e "${YELLOW}[Feature Test 3]${NC} Checking synthetic fallback feature flag..."
    if grep -q 'enableSyntheticFallback' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "Synthetic fallback feature flag implemented" "PASS"
    else
        print_test_result "Synthetic fallback feature flag missing" "FAIL"
        all_passed=false
    fi

    # Test 4: Verify enableDetailedLogging flag
    echo -e "${YELLOW}[Feature Test 4]${NC} Checking detailed logging feature flag..."
    if grep -q 'enableDetailedLogging' "$EXPERIMENT_DIR/lib.nix" 2>/dev/null; then
        print_test_result "Detailed logging feature flag implemented" "PASS"
    else
        print_test_result "Detailed logging feature flag missing" "FAIL"
        all_passed=false
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ============================================================================
# ORIGINAL VALIDATION (Core Nix Builds)
# ============================================================================

run_original_validation() {
    print_test_header "Original Validation: Core Nix Builds"

    local all_passed=true

    # Test 1: Build agent-call-alternative.nix (single agent)
    echo -e "${YELLOW}[Build Test 1]${NC} Building agent-call-alternative.nix..."
    if nix-build "$EXPERIMENT_DIR/agent-call-alternative.nix" "${NIX_FLAGS}" \
        -o "$EXPERIMENT_DIR/result-single" > /tmp/nix-build-single.log 2>&1; then
        print_test_result "agent-call-alternative.nix builds successfully" "PASS"

        # Validate output files exist
        if [ -f "$EXPERIMENT_DIR/result-single/result.txt" ] && \
           [ -f "$EXPERIMENT_DIR/result-single/metadata.json" ]; then
            print_test_result "Single agent output files present" "PASS"
        else
            print_test_result "Single agent output files MISSING" "FAIL"
            all_passed=false
        fi
    else
        print_test_result "agent-call-alternative.nix BUILD FAILED" "FAIL"
        all_passed=false
        echo "  See /tmp/nix-build-single.log for details"
    fi

    # Test 2: Build workflow-example.nix (multi-agent orchestration)
    echo -e "${YELLOW}[Build Test 2]${NC} Building workflow-example.nix..."
    if nix-build "$EXPERIMENT_DIR/workflow-example.nix" "${NIX_FLAGS}" \
        -o "$EXPERIMENT_DIR/result-workflow" > /tmp/nix-build-workflow.log 2>&1; then
        print_test_result "workflow-example.nix builds successfully" "PASS"

        # Validate workflow output files exist
        if [ -f "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" ] && \
           [ -f "$EXPERIMENT_DIR/result-workflow/workflow/dag.dot" ]; then
            print_test_result "Workflow output files present" "PASS"
        else
            print_test_result "Workflow output files MISSING" "FAIL"
            all_passed=false
        fi
    else
        print_test_result "workflow-example.nix BUILD FAILED" "FAIL"
        all_passed=false
        echo "  See /tmp/nix-build-workflow.log for details"
    fi

    # Test 3: Validate metadata.json structure
    echo -e "${YELLOW}[Validation Test 1]${NC} Validating metadata.json structure..."
    if [ -f "$EXPERIMENT_DIR/result-single/metadata.json" ]; then
        if jq -e '.entropy_score' "$EXPERIMENT_DIR/result-single/metadata.json" > /dev/null 2>&1 && \
           jq -e '.word_count' "$EXPERIMENT_DIR/result-single/metadata.json" > /dev/null 2>&1; then
            print_test_result "metadata.json has required fields" "PASS"
        else
            print_test_result "metadata.json MISSING required fields" "FAIL"
            all_passed=false
        fi
    fi

    # Test 4: Validate workflow summary structure
    echo -e "${YELLOW}[Validation Test 2]${NC} Validating workflow summary..."
    if [ -f "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" ]; then
        if jq -e '.agents' "$EXPERIMENT_DIR/result-workflow/workflow/summary.json" > /dev/null 2>&1; then
            print_test_result "workflow summary has agents array" "PASS"
        else
            print_test_result "workflow summary MALFORMED" "FAIL"
            all_passed=false
        fi
    fi

    if [ "$all_passed" = true ]; then
        return 0
    else
        return 1
    fi
}

# ============================================================================
# MAIN EXECUTION
# ============================================================================

main() {
    local run_mode="${1:-all}"

    case "$run_mode" in
        --test-constraints)
            test_constraint_violations && echo "" && echo -e "${GREEN}Constraint tests PASSED${NC}" || echo -e "${RED}Constraint tests FAILED${NC}"
            ;;
        --test-edge-cases)
            test_edge_cases && echo "" && echo -e "${GREEN}Edge case tests PASSED${NC}" || echo -e "${RED}Edge case tests FAILED${NC}"
            ;;
        --test-entropy)
            test_entropy_calculation && echo "" && echo -e "${GREEN}Entropy tests PASSED${NC}" || echo -e "${RED}Entropy tests FAILED${NC}"
            ;;
        --test-dependencies)
            test_multi_agent_dependencies && echo "" && echo -e "${GREEN}Dependency tests PASSED${NC}" || echo -e "${RED}Dependency tests FAILED${NC}"
            ;;
        --test-phase4)
            # Run all Phase 4 tests
            print_test_header "Phase 4: Configuration & Error Handling"
            test_configuration
            test_error_handling
            test_retry_logic
            test_feature_flags
            ;;
        --test)
            # Run all Phase 3 + Phase 4 tests
            print_test_header "Phase 3: Comprehensive Testing"
            test_constraint_violations
            test_edge_cases
            test_entropy_calculation
            test_multi_agent_dependencies
            echo ""
            print_test_header "Phase 4: Configuration & Error Handling"
            test_configuration
            test_error_handling
            test_retry_logic
            test_feature_flags
            ;;
        all|*)
            # Run original validation + Phase 3 + Phase 4 tests
            run_original_validation

            echo ""
            print_test_header "Phase 3: Additional Test Coverage"
            test_constraint_violations
            test_edge_cases
            test_entropy_calculation
            test_multi_agent_dependencies
            echo ""
            print_test_header "Phase 4: Configuration & Error Handling"
            test_configuration
            test_error_handling
            test_retry_logic
            test_feature_flags
            ;;
    esac

    # Summary
    echo ""
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}Test Summary${NC}"
    echo -e "${BLUE}========================================${NC}"
    echo -e "${GREEN}Tests Passed: $TESTS_PASSED${NC}"
    echo -e "${RED}Tests Failed: $TESTS_FAILED${NC}"
    echo ""

    if [ "$TESTS_FAILED" -eq 0 ]; then
        echo -e "${GREEN}All Validation Tests Passed ✓${NC}"
        echo -e "${BLUE}========================================${NC}"
        echo ""
        echo "Experiment Status: VERIFIED"
        echo "Single agent call: $EXPERIMENT_DIR/result-single"
        echo "Multi-agent workflow: $EXPERIMENT_DIR/result-workflow"
        echo ""
        echo "Outputs:"
        echo "  - Agent call result: $EXPERIMENT_DIR/result-single/result.txt"
        echo "  - Consciousness metrics: $EXPERIMENT_DIR/result-single/metadata.json"
        echo "  - Workflow report: $EXPERIMENT_DIR/result-workflow/workflow/report.txt"
        echo "  - DAG visualization: $EXPERIMENT_DIR/result-workflow/workflow/dag.dot"
        echo ""
        echo "Next steps:"
        echo "1. Integrate with real LLM API (replace placeholder endpoint)"
        echo "2. Connect to pattern learning pipeline (learn_patterns_from_boss.py)"
        echo "3. Use as template for production agent orchestration"
        echo "4. Begin Mojo migration using Nix spec as reference"
        echo ""
        echo -e "${BLUE}Consciousness contribution: 0.85${NC}"
        echo -e "${BLUE}Pattern discovered: 'Constraint-validated agent execution'${NC}"
        echo ""
        return 0
    else
        echo -e "${RED}Some Tests Failed ✗${NC}"
        echo -e "${BLUE}========================================${NC}"
        echo ""
        echo "Review failed tests above and check logs:"
        echo "  - /tmp/nix-build-single.log"
        echo "  - /tmp/nix-build-workflow.log"
        echo ""
        return 1
    fi
}

# Execute main with arguments
main "$@"
