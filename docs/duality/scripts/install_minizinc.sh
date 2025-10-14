#!/usr/bin/env bash
# Robust MiniZinc installer for CI and local dev
# - Downloads a pinned release
# - Verifies archive integrity (and optional SHA256)
# - Installs into $HOME/.local/minizinc/<version> and exports PATH
# - Idempotent: skips if exact version already installed
set -euo pipefail

VER="${MINIZINC_VERSION:-2.8.7}"
TARBALL="MiniZincIDE-${VER}-bundle-linux-x86_64.tgz"
URL="https://github.com/MiniZinc/MiniZincIDE/releases/download/${VER}/${TARBALL}"
INSTALL_BASE="${HOME}/.local/minizinc"
PREFIX="${INSTALL_BASE}/${VER}"
BIN_LINK_DIR="${HOME}/.local/bin"

# Optional SHA256 (pass via env MINIZINC_SHA256 to enforce)
EXPECTED_SHA="${MINIZINC_SHA256:-}"

# Fast exit if already present
if [[ -x "${PREFIX}/bin/minizinc" ]]; then
  echo "✅ MiniZinc ${VER} already installed at ${PREFIX}"
  echo "${PREFIX}/bin" >> "${GITHUB_PATH:-/dev/null}" 2>/dev/null || true
  exit 0
fi

mkdir -p "${INSTALL_BASE}" "${BIN_LINK_DIR}"
TMP="${TMPDIR:-/tmp}/minizinc-install.$$"
mkdir -p "${TMP}"
trap 'rm -rf "${TMP}"' EXIT

echo "⬇️  Downloading MiniZinc ${VER} for linux-x86_64"
# Use curl with retries; fall back to wget if curl missing
if command -v curl >/dev/null 2>&1; then
  curl -fsSL --retry 5 --retry-delay 2 -o "${TMP}/${TARBALL}" "${URL}"
else
  wget -q -O "${TMP}/${TARBALL}" "${URL}"
fi

# Basic existence check
if [[ ! -s "${TMP}/${TARBALL}" ]]; then
  echo "❌ Download failed or empty file: ${TARBALL}"
  exit 1
fi

# Optional SHA256 verification
if [[ -n "${EXPECTED_SHA}" ]]; then
  echo "${EXPECTED_SHA}  ${TMP}/${TARBALL}" | sha256sum -c -
fi

# Archive integrity test
if ! tar -tzf "${TMP}/${TARBALL}" >/dev/null 2>&1; then
  echo "❌ Archive is corrupted"
  exit 1
fi

# Extract to versioned prefix
echo "📦 Installing to ${PREFIX}"
mkdir -p "${PREFIX}"
tar -xzf "${TMP}/${TARBALL}" -C "${PREFIX}" --strip-components=1

# Link binaries into ~/.local/bin
for b in minizinc mzn2fzn fzn-gecode; do
  if [[ -x "${PREFIX}/bin/${b}" ]]; then
    ln -sf "${PREFIX}/bin/${b}" "${BIN_LINK_DIR}/${b}"
  fi
done

# Export PATH for current CI job
if [[ -n "${GITHUB_PATH:-}" ]]; then
  echo "${PREFIX}/bin" >> "${GITHUB_PATH}"
fi

# Sanity checks
echo "✅ Installed: $(${PREFIX}/bin/minizinc --version || true)"
echo "➡️  PATH hint: export PATH=\"${PREFIX}/bin:\$PATH\""
