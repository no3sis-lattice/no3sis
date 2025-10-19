# Cargo Workspace Management

Guidelines for managing Rust workspaces effectively in complex projects.

## Workspace Structure

### Basic Workspace Setup
```toml
# Cargo.toml (workspace root)
[workspace]
members = [
    "crates/core",
    "crates/api",
    "crates/cli",
    "examples/*"
]
exclude = ["target", "archive/*"]

[workspace.dependencies]
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
anyhow = "1.0"
```

### Member Crate Structure
```toml
# crates/core/Cargo.toml
[package]
name = "my-project-core"
version.workspace = true
edition.workspace = true

[dependencies]
tokio = { workspace = true }
serde = { workspace = true }
anyhow = { workspace = true }
```

## Best Practices

### 1. Workspace Organization
- **Core Logic**: `crates/core/` - shared business logic
- **API Layer**: `crates/api/` - web API or service interface
- **CLI Tools**: `crates/cli/` - command-line interfaces
- **Examples**: `examples/` - usage examples and demos
- **Tools**: `tools/` - development and build tools

### 2. Dependency Management
- Use `workspace.dependencies` for version consistency
- Pin exact versions for reproducible builds
- Group related dependencies by purpose
- Use feature flags to minimize compilation units

### 3. Testing Strategy
```bash
# Run all workspace tests
cargo test --workspace

# Test specific crate
cargo test -p my-project-core

# Integration tests
cargo test --workspace --test integration
```

### 4. Build Optimization
```toml
[profile.dev]
opt-level = 0
debug = true
incremental = true

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"
```

## Common Commands

### Development Workflow
```bash
# Build entire workspace
cargo build --workspace

# Check all crates
cargo check --workspace

# Format workspace code
cargo fmt --all

# Run clippy on workspace
cargo clippy --workspace -- -D warnings

# Update dependencies
cargo update
```

### Publishing Workflow
```bash
# Dry run publish
cargo publish --dry-run -p crate-name

# Publish in dependency order
cargo publish -p my-project-core
cargo publish -p my-project-api
cargo publish -p my-project-cli
```

## Troubleshooting

### Common Issues
1. **Circular Dependencies**: Review crate boundaries and extract shared code
2. **Version Conflicts**: Use `cargo tree -d` to identify conflicts
3. **Build Times**: Optimize with `sccache` and proper feature flags
4. **Target Directory**: Use `CARGO_TARGET_DIR` for shared builds