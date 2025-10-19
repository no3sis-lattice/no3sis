# Rust Error Handling Patterns

Comprehensive guide to robust error handling in Rust applications.

## Core Error Types

### Using anyhow for Applications
```rust
use anyhow::{Context, Result};

fn process_file(path: &str) -> Result<String> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read file: {}", path))?;

    let processed = content
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n");

    Ok(processed)
}
```

### Custom Error Types for Libraries
```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid header at line {line}")]
    InvalidHeader { line: usize },

    #[error("Missing field: {field}")]
    MissingField { field: String },

    #[error("IO error")]
    Io(#[from] std::io::Error),

    #[error("Parse error")]
    Parse(#[from] serde_json::Error),
}

pub type Result<T> = std::result::Result<T, ParseError>;
```

## Error Propagation Patterns

### The ? Operator
```rust
fn chain_operations() -> Result<String> {
    let config = load_config()?;
    let data = fetch_data(&config.url)?;
    let result = process_data(data)?;
    Ok(result)
}
```

### Error Context Addition
```rust
fn with_context_example() -> Result<Data> {
    let raw_data = fetch_raw_data()
        .context("Failed to fetch raw data from API")?;

    let parsed = parse_data(&raw_data)
        .with_context(|| format!("Failed to parse {} bytes of data", raw_data.len()))?;

    Ok(parsed)
}
```

## Async Error Handling

### With Tokio and anyhow
```rust
use anyhow::Result;
use tokio::fs;

async fn async_file_processing() -> Result<()> {
    let files = vec!["file1.txt", "file2.txt", "file3.txt"];

    for file in files {
        let content = fs::read_to_string(file)
            .await
            .with_context(|| format!("Failed to read {}", file))?;

        process_content(&content)
            .await
            .with_context(|| format!("Failed to process {}", file))?;
    }

    Ok(())
}
```

### Error Collection with join_all
```rust
use futures::future::join_all;

async fn parallel_processing() -> Result<Vec<String>> {
    let urls = vec!["url1", "url2", "url3"];

    let futures = urls.into_iter().map(|url| {
        async move {
            fetch_data(url)
                .await
                .with_context(|| format!("Failed to fetch from {}", url))
        }
    });

    let results: Result<Vec<_>> = join_all(futures)
        .await
        .into_iter()
        .collect();

    results
}
```

## Error Recovery Strategies

### Retry Logic
```rust
use std::time::Duration;
use tokio::time::sleep;

async fn retry_with_backoff<F, T, E>(
    mut operation: F,
    max_retries: usize,
) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut attempts = 0;

    loop {
        match operation() {
            Ok(result) => return Ok(result),
            Err(e) if attempts >= max_retries => return Err(e),
            Err(_) => {
                attempts += 1;
                let delay = Duration::from_millis(100 * 2_u64.pow(attempts as u32));
                sleep(delay).await;
            }
        }
    }
}
```

### Fallback Values
```rust
fn with_fallback(config_path: &str) -> Config {
    load_config(config_path)
        .or_else(|_| load_default_config())
        .unwrap_or_default()
}
```

## Testing Error Scenarios

### Unit Testing Errors
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_error() {
        let invalid_input = "invalid data";
        let result = parse_data(invalid_input);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ParseError::InvalidHeader { .. }));
    }

    #[tokio::test]
    async fn test_network_error() {
        let result = fetch_data("invalid_url").await;
        assert!(result.is_err());
    }
}
```

## Logging and Error Reporting

### Structured Logging
```rust
use tracing::{error, info, warn};

fn process_with_logging() -> Result<()> {
    info!("Starting data processing");

    match dangerous_operation() {
        Ok(result) => {
            info!(result_count = result.len(), "Processing completed successfully");
            Ok(())
        }
        Err(e) => {
            error!(error = %e, "Processing failed");
            Err(e)
        }
    }
}
```

## Best Practices

1. **Use anyhow for applications, thiserror for libraries**
2. **Add context to errors as they propagate up**
3. **Design error types around caller needs, not implementation details**
4. **Use structured logging for error investigation**
5. **Test error paths explicitly**
6. **Consider error recovery strategies early in design**
7. **Use type system to make impossible states unrepresentable**