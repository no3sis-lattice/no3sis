#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

SUBTREE_DIR="docs/duality"
REMOTE_NAME="${REMOTE_NAME:-duality}"
REMOTE_URL="${REMOTE_URL:-git@github.com:noesis-lattice/duality-formalization.git}"
TARGET_BRANCH="${TARGET_BRANCH:-master}"  # change to main if you switch later
TMP_BRANCH="duality-tmp-push"

if [ ! -d "$SUBTREE_DIR" ]; then
  echo "Error: $SUBTREE_DIR not found."
  exit 1
fi

# Ensure the remote exists (idempotent)
if ! git remote | grep -qx "$REMOTE_NAME"; then
  git remote add "$REMOTE_NAME" "$REMOTE_URL"
fi

git fetch "$REMOTE_NAME" --prune

# Clean any stale tmp branch locally
git branch -D "$TMP_BRANCH" 2>/dev/null || true

# Split the subtree to a temporary branch and push it
git subtree split --prefix="$SUBTREE_DIR" -b "$TMP_BRANCH"
git push "$REMOTE_NAME" "$TMP_BRANCH:$TARGET_BRANCH"

# Cleanup
git branch -D "$TMP_BRANCH" || true

echo "Published $SUBTREE_DIR to $REMOTE_NAME/$TARGET_BRANCH"
