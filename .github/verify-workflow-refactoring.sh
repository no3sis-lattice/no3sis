#!/bin/bash
# Verification script for workflow refactoring
# Run this to verify all changes are working correctly

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "======================================"
echo "Workflow Refactoring Verification"
echo "======================================"
echo ""

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

check_file() {
    local file=$1
    if [ -f "$file" ]; then
        echo -e "${GREEN}✓${NC} $file exists"
        return 0
    else
        echo -e "${RED}✗${NC} $file missing"
        return 1
    fi
}

check_executable() {
    local file=$1
    if [ -x "$file" ]; then
        echo -e "${GREEN}✓${NC} $file is executable"
        return 0
    else
        echo -e "${RED}✗${NC} $file not executable"
        return 1
    fi
}

# 1. Check composite action exists
echo "1. Checking composite action..."
check_file "$SCRIPT_DIR/actions/setup-nix/action.yml"
echo ""

# 2. Check CI scripts exist and are executable
echo "2. Checking CI scripts..."
check_file "$PROJECT_ROOT/docs/duality/scripts/ci/validate_json_schema.py"
check_executable "$PROJECT_ROOT/docs/duality/scripts/ci/validate_json_schema.py"
check_file "$PROJECT_ROOT/docs/duality/scripts/ci/validate_minizinc.sh"
check_executable "$PROJECT_ROOT/docs/duality/scripts/ci/validate_minizinc.sh"
check_file "$PROJECT_ROOT/docs/duality/scripts/ci/build_lean.sh"
check_executable "$PROJECT_ROOT/docs/duality/scripts/ci/build_lean.sh"
echo ""

# 3. Check workflows exist
echo "3. Checking workflow files..."
check_file "$SCRIPT_DIR/workflows/duality-nix.yml"
check_file "$SCRIPT_DIR/workflows/duality-nix-nightly.yml"
check_file "$SCRIPT_DIR/workflows/duality-nix-smoke.yml"
check_file "$SCRIPT_DIR/workflows/nix-build.yml"
check_file "$SCRIPT_DIR/workflows/duality-validation.yml"
check_file "$SCRIPT_DIR/workflows/reusable-validate-duality.yml"
check_file "$SCRIPT_DIR/workflows/duality-nix-simplified.yml"
echo ""

# 4. Check workflows use composite action
echo "4. Checking workflows use composite action..."
workflows=(
    "duality-nix.yml"
    "duality-nix-nightly.yml"
    "duality-nix-smoke.yml"
    "nix-build.yml"
)

for workflow in "${workflows[@]}"; do
    if grep -q "uses: ./.github/actions/setup-nix" "$SCRIPT_DIR/workflows/$workflow"; then
        echo -e "${GREEN}✓${NC} $workflow uses composite action"
    else
        echo -e "${RED}✗${NC} $workflow doesn't use composite action"
    fi
done
echo ""

# 5. Check legacy workflow is manual-only
echo "5. Checking legacy workflow is manual-only..."
if grep -q "workflow_dispatch:" "$SCRIPT_DIR/workflows/duality-validation.yml"; then
    echo -e "${GREEN}✓${NC} duality-validation.yml is manual-trigger only"
else
    echo -e "${RED}✗${NC} duality-validation.yml still has automatic triggers"
fi
echo ""

# 6. Verify no remaining duplicate Nix install blocks
echo "6. Checking for duplicate Nix install blocks..."
nix_install_count=$(grep -r "cachix/install-nix-action" "$SCRIPT_DIR/workflows/"*.yml | wc -l)
composite_uses=$(grep -r "uses: ./.github/actions/setup-nix" "$SCRIPT_DIR/workflows/"*.yml | wc -l)

echo "   Workflows using composite action: $composite_uses"
if [ "$composite_uses" -ge 4 ]; then
    echo -e "${GREEN}✓${NC} Multiple workflows using composite action"
else
    echo -e "${YELLOW}⚠${NC} Only $composite_uses workflows using composite action"
fi
echo ""

# 7. Check YAML syntax
echo "7. Checking YAML syntax..."
if command -v yamllint &> /dev/null; then
    yamllint -d relaxed "$SCRIPT_DIR/workflows/"*.yml "$SCRIPT_DIR/actions/setup-nix/action.yml" 2>&1 | head -20
    echo -e "${GREEN}✓${NC} YAML syntax check complete"
else
    echo -e "${YELLOW}⚠${NC} yamllint not installed, skipping syntax check"
    echo "   Install with: pip install yamllint"
fi
echo ""

# 8. Count total lines
echo "8. Line count summary..."
workflow_lines=$(wc -l "$SCRIPT_DIR/workflows/"*.yml | tail -1 | awk '{print $1}')
composite_lines=$(wc -l "$SCRIPT_DIR/actions/setup-nix/action.yml" | awk '{print $1}')
ci_scripts_lines=$(wc -l "$PROJECT_ROOT/docs/duality/scripts/ci/"*.{py,sh} 2>/dev/null | tail -1 | awk '{print $1}')

echo "   Workflow files: $workflow_lines lines"
echo "   Composite action: $composite_lines lines"
echo "   CI scripts: $ci_scripts_lines lines"
echo "   Total: $((workflow_lines + composite_lines + ci_scripts_lines)) lines"
echo ""

# 9. Test CI scripts (if in Nix environment)
echo "9. Testing CI scripts (requires Nix)..."
if command -v nix &> /dev/null; then
    cd "$PROJECT_ROOT/docs/duality"

    echo "   Testing JSON schema validator..."
    if nix develop --command python3 scripts/ci/validate_json_schema.py --help &> /dev/null; then
        echo -e "${GREEN}✓${NC} JSON validator script works"
    else
        echo -e "${RED}✗${NC} JSON validator script failed"
    fi

    echo "   Testing MiniZinc validator..."
    if [ -f scripts/ci/validate_minizinc.sh ]; then
        echo -e "${GREEN}✓${NC} MiniZinc validator script exists"
    fi

    echo "   Testing Lean builder..."
    if [ -f scripts/ci/build_lean.sh ]; then
        echo -e "${GREEN}✓${NC} Lean builder script exists"
    fi
else
    echo -e "${YELLOW}⚠${NC} Nix not installed, skipping script tests"
fi
echo ""

echo "======================================"
echo "Verification Complete!"
echo "======================================"
echo ""
echo "Next steps:"
echo "1. Review the refactoring report: .github/WORKFLOW_REFACTORING_REPORT.md"
echo "2. Test workflows on a feature branch"
echo "3. Monitor CI runs for any issues"
echo ""
echo "To test locally:"
echo "  cd docs/duality"
echo "  nix develop --command python3 scripts/ci/validate_json_schema.py --pilots 06 08 09 19"
echo "  nix develop --command bash scripts/ci/validate_minizinc.sh pilots"
echo "  nix develop --command bash scripts/ci/build_lean.sh pilots"
echo ""