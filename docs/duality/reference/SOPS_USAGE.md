# SOPS Usage Guide - Duality Subsystem

**Phase 6**: Encrypted secret management standard for Synapse duality subsystem

---

## Overview

SOPS (Secrets OPerationS) is the standard for managing encrypted secrets in the duality subsystem. All sensitive data (API keys, tokens, credentials) must be encrypted with SOPS before committing to the repository.

**Key Features**:
- ✅ Age-encrypted (modern, simple cryptography)
- ✅ Git-friendly (encrypted YAML can be diffed/merged)
- ✅ Editor integration (decrypt → edit → encrypt automatically)
- ✅ CI-ready (decrypt secrets in GitHub Actions)

---

## Installation

### 1. Install SOPS

```bash
# macOS
brew install sops

# Linux
# Download latest from https://github.com/getsops/sops/releases
wget https://github.com/getsops/sops/releases/download/v3.8.1/sops-v3.8.1.linux.amd64
sudo mv sops-v3.8.1.linux.amd64 /usr/local/bin/sops
sudo chmod +x /usr/local/bin/sops

# Verify installation
sops --version
```

###  Install age (encryption tool)

```bash
# macOS
brew install age

# Linux
# Download latest from https://github.com/FiloSottile/age/releases
wget https://github.com/FiloSottile/age/releases/download/v1.1.1/age-v1.1.1-linux-amd64.tar.gz
tar xzf age-v1.1.1-linux-amd64.tar.gz
sudo mv age/age /usr/local/bin/
sudo chmod +x /usr/local/bin/age

# Verify installation
age --version
```

---

## Setup

### 1. Generate Age Key (One-Time)

```bash
# Generate new age keypair
age-keygen -o ~/.age/duality-ci.key

# Example output:
# Public key: age15ss3edcg6ejg2mapcnucugnsegcyrs23tzts55jdmtv5wjshha6qy9e0m9
# (key saved to ~/.age/duality-ci.key)
```

**IMPORTANT**:
- Keep `~/.age/duality-ci.key` PRIVATE (never commit this!)
- The public key is already in `.sops.yaml` (committed to repo)
- If you generate a new key, update `.sops.yaml` with the new public key

### 2. Configure Environment

Add to your `.bashrc` or `.zshrc`:

```bash
# SOPS age key for duality subsystem
export SOPS_AGE_KEY_FILE="$HOME/.age/duality-ci.key"
```

Reload shell:
```bash
source ~/.bashrc  # or source ~/.zshrc
```

### 3. Verify Setup

```bash
# Check age key is loaded
echo $SOPS_AGE_KEY_FILE
# Should output: /home/username/.age/duality-ci.key

# Verify SOPS can access key
sops --version
```

---

## Usage

### Encrypting a New Secrets File

**Method 1: Create plain file, then encrypt**

```bash
# 1. Create plain YAML file
cat > .github/workflows/secrets/my-service.sops.yaml <<EOF
api_key: "sk-1234567890abcdef"
database_url: "postgresql://user:password@localhost/db"
EOF

# 2. Encrypt in-place
sops -e -i .github/workflows/secrets/my-service.sops.yaml

# 3. Verify encryption
head -20 .github/workflows/secrets/my-service.sops.yaml
# Should show encrypted blobs and SOPS metadata
```

**Method 2: Use example template**

```bash
# 1. Copy example template
cp .github/workflows/secrets/example.sops.yaml .github/workflows/secrets/my-service.sops.yaml

# 2. Edit template (still unencrypted)
vim .github/workflows/secrets/my-service.sops.yaml
# Replace EXAMPLE_* placeholders with real values

# 3. Encrypt
sops -e -i .github/workflows/secrets/my-service.sops.yaml
```

### Editing Encrypted Secrets

**SOPS automatically decrypts for editing, re-encrypts on save:**

```bash
# Edit encrypted file (magic!)
sops .github/workflows/secrets/duality-ci.sops.yaml

# SOPS will:
# 1. Decrypt file
# 2. Open in $EDITOR (vim/nano/etc)
# 3. Re-encrypt when you save and exit
```

### Decrypting (Read-Only)

```bash
# Decrypt to stdout (does NOT modify file)
sops -d .github/workflows/secrets/duality-ci.sops.yaml

# Decrypt to temporary file
sops -d .github/workflows/secrets/duality-ci.sops.yaml > /tmp/secrets.yaml

# Use decrypted values in script
eval $(sops -d --output-type dotenv .github/workflows/secrets/duality-ci.sops.yaml)
echo $api_key  # Now available as environment variable
```

### Verifying Encryption

```bash
# Check if file is encrypted
file .github/workflows/secrets/duality-ci.sops.yaml
# Should output: ASCII text (not binary)

# Check SOPS metadata exists
grep "sops:" .github/workflows/secrets/duality-ci.sops.yaml
# Should show SOPS metadata block

# Verify values are encrypted
grep -E "(api_key|password|token):" .github/workflows/secrets/duality-ci.sops.yaml
# Values should be encrypted blobs like: ENC[AES256_GCM,data:...]
```

---

## CI Integration (GitHub Actions)

### 1. Add SOPS Age Key to GitHub Secrets

**Location**: Repository → Settings → Secrets and variables → Actions → New repository secret

**Name**: `SOPS_AGE_KEY`

**Value**: Paste content of `~/.age/duality-ci.key`

```bash
# Get your private key
cat ~/.age/duality-ci.key

# Example output:
# AGE-SECRET-KEY-1QYQSZQGPQYQSZQGPQYQSZQGPQYQSZQGPQYQSZQGPQYQSZ...

# Copy the entire key (including header) and paste into GitHub secret
```

### 2. Decrypt Secrets in Workflow

Example from `duality-nix.yml`:

```yaml
- name: Setup SOPS
  uses: mdgreenwald/mozilla-sops-action@v1.6.0

- name: Decrypt CI Secrets
  run: |
    sops -d .github/workflows/secrets/duality-ci.sops.yaml > /tmp/secrets.yaml
    echo "✓ Secrets decrypted"
  env:
    SOPS_AGE_KEY: ${{ secrets.SOPS_AGE_KEY }}

- name: Load Secrets to Environment
  run: |
    # Parse YAML and export as env vars
    eval $(sops -d --output-type dotenv .github/workflows/secrets/duality-ci.sops.yaml)
    echo "API_KEY=$api_key" >> $GITHUB_ENV
```

---

## File Structure

```
.
├── .sops.yaml                              # SOPS config (age recipient)
└── .github/workflows/secrets/
    ├── duality-ci.sops.yaml                # Duality CI secrets (Phase 6)
    ├── example.sops.yaml                   # Template for new secrets
    └── <your-service>.sops.yaml           # Additional secrets as needed
```

### `.sops.yaml` Configuration

```yaml
creation_rules:
  - path_regex: .*\.yaml$
    age: age15ss3edcg6ejg2mapcnucugnsegcyrs23tzts55jdmtv5wjshha6qy9e0m9
```

**Explanation**:
- `path_regex`: Encrypt all `.yaml` files in repo
- `age`: Public key for encryption (corresponds to private key in `~/.age/duality-ci.key`)

---

## Security Best Practices

### ✅ DO

- **Always encrypt before committing**: `sops -e -i <file>`
- **Use age keys (not PGP)**: Simpler, more secure
- **Keep private key secure**: `~/.age/duality-ci.key` should be `chmod 600`
- **Use descriptive filenames**: `github-api.sops.yaml` not `secrets.sops.yaml`
- **Commit encrypted files to git**: Safe to commit `.sops.yaml` files
- **Use separate keys for different environments**: prod vs dev vs CI

### ❌ DON'T

- **Never commit unencrypted secrets**: Always run `sops -e -i` first
- **Never commit private age key**: `~/.age/duality-ci.key` stays local
- **Never share age private key via Slack/email**: Use secure channels only
- **Don't encrypt non-secret data**: Only use SOPS for actual secrets
- **Don't use same key across multiple repos**: Generate new key per project

---

## Troubleshooting

### Error: "no key could decrypt the data"

**Cause**: SOPS can't find your private age key

**Solution**:
```bash
# Check environment variable
echo $SOPS_AGE_KEY_FILE
# Should show: /home/username/.age/duality-ci.key

# If not set:
export SOPS_AGE_KEY_FILE="$HOME/.age/duality-ci.key"

# Or use inline:
SOPS_AGE_KEY_FILE=~/.age/duality-ci.key sops -d file.sops.yaml
```

### Error: "sops metadata not found"

**Cause**: File is not encrypted yet

**Solution**:
```bash
# Encrypt the file
sops -e -i .github/workflows/secrets/my-file.sops.yaml

# Verify encryption
grep "sops:" .github/workflows/secrets/my-file.sops.yaml
```

### Error: "age: failed to decrypt"

**Cause**: Wrong private key or file encrypted with different public key

**Solution**:
1. Check public key in `.sops.yaml` matches your private key:
   ```bash
   age-keygen -y ~/.age/duality-ci.key
   # Should match public key in .sops.yaml
   ```

2. If keys don't match, you need to:
   - Get the correct private key from original encryptor, OR
   - Re-encrypt file with your key (requires plain values)

### CI Failure: "SOPS_AGE_KEY not set"

**Cause**: GitHub secret not configured

**Solution**:
1. Go to repo Settings → Secrets → Actions
2. Add new secret: `SOPS_AGE_KEY`
3. Paste content of `~/.age/duality-ci.key`
4. Re-run workflow

---

## Examples

### Example 1: Add Cachix Token

```bash
# 1. Edit duality-ci.sops.yaml
sops .github/workflows/secrets/duality-ci.sops.yaml

# 2. Replace placeholder in cachix section:
# Before:
#   cachix:
#     auth_token: "PLACEHOLDER_WILL_BE_ENCRYPTED_WHEN_CACHIX_IS_SETUP"

# After:
#   cachix:
#     auth_token: "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."  # Real token

# 3. Save and exit (SOPS auto-encrypts)

# 4. Commit
git add .github/workflows/secrets/duality-ci.sops.yaml
git commit -m "Add Cachix authentication token"
git push
```

### Example 2: Add New Service Secrets

```bash
# 1. Copy template
cp .github/workflows/secrets/example.sops.yaml .github/workflows/secrets/no3sis-mcp.sops.yaml

# 2. Edit plain file
vim .github/workflows/secrets/no3sis-mcp.sops.yaml
# Add real values for No3sis MCP integration

# 3. Encrypt
sops -e -i .github/workflows/secrets/no3sis-mcp.sops.yaml

# 4. Use in workflow
# .github/workflows/duality-nix.yml:
#   - name: Load No3sis Secrets
#     run: |
#       eval $(sops -d --output-type dotenv .github/workflows/secrets/no3sis-mcp.sops.yaml)
#       echo "NO3SIS_API_KEY=$api_key" >> $GITHUB_ENV
```

### Example 3: Rotate Secrets

```bash
# 1. Edit encrypted file
sops .github/workflows/secrets/duality-ci.sops.yaml

# 2. Update values (e.g., rotate API key)
# Old: api_key: "sk-old-key-12345"
# New: api_key: "sk-new-key-67890"

# 3. Save and exit (auto-encrypts)

# 4. Commit rotation
git add .github/workflows/secrets/duality-ci.sops.yaml
git commit -m "Rotate API keys per security policy"
git push
```

---

## Resources

- **SOPS GitHub**: https://github.com/getsops/sops
- **Age GitHub**: https://github.com/FiloSottile/age
- **SOPS + Age Tutorial**: https://dev.to/stack-labs/manage-your-secrets-in-git-with-sops-common-operations-118g
- **GitHub Actions SOPS**: https://github.com/mdgreenwald/mozilla-sops-action

---

## Summary

**Phase 6 Status**: SOPS infrastructure established ✅

- `.sops.yaml` configured with age encryption
- `duality-ci.sops.yaml` created with placeholders
- `example.sops.yaml` template provided
- GitHub Actions integration ready
- Zero secrets exist yet (all placeholders)

**Next Steps**:
1. User encrypts `duality-ci.sops.yaml`: `sops -e -i .github/workflows/secrets/duality-ci.sops.yaml`
2. User adds `SOPS_AGE_KEY` to GitHub repo secrets
3. Future integrations replace placeholders with real values

**Encryption is now the standard** - all secrets must use SOPS before committing.
