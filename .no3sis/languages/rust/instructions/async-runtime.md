# Async Runtime Patterns in Rust

Best practices for building efficient asynchronous applications with Tokio and async/await.

## Runtime Configuration

### Basic Tokio Setup
```rust
// For applications
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Application logic here
    Ok(())
}

// Custom runtime configuration
use tokio::runtime::Runtime;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let rt = Runtime::new()?;
    rt.block_on(async {
        // Async application logic
    })
}
```

### Multi-threaded Runtime
```rust
use tokio::runtime::Builder;

fn create_custom_runtime() -> std::io::Result<Runtime> {
    Builder::new_multi_thread()
        .worker_threads(4)
        .thread_name("my-app")
        .thread_stack_size(3 * 1024 * 1024)
        .enable_all()
        .build()
}
```

## Async Patterns

### Concurrent Execution
```rust
use tokio::join;

async fn concurrent_operations() -> Result<(String, Vec<u8>, i32)> {
    let (result1, result2, result3) = join!(
        fetch_text_data(),
        fetch_binary_data(),
        compute_value()
    );

    Ok((result1?, result2?, result3?))
}
```

### Select for Racing Operations
```rust
use tokio::select;
use tokio::time::{timeout, Duration};

async fn race_with_timeout() -> Result<String> {
    select! {
        result = fetch_data() => {
            result.context("Data fetch failed")
        }
        _ = tokio::time::sleep(Duration::from_secs(10)) => {
            Err(anyhow::anyhow!("Operation timed out"))
        }
    }
}
```

### Spawning Tasks
```rust
use tokio::task::JoinHandle;

async fn spawn_background_tasks() -> Result<Vec<String>> {
    let handles: Vec<JoinHandle<Result<String>>> = (0..10)
        .map(|i| {
            tokio::spawn(async move {
                process_item(i).await
            })
        })
        .collect();

    let mut results = Vec::new();
    for handle in handles {
        results.push(handle.await??);
    }

    Ok(results)
}
```

## Channel Communication

### mpsc for Producer-Consumer
```rust
use tokio::sync::mpsc;

async fn producer_consumer_pattern() {
    let (tx, mut rx) = mpsc::channel::<String>(100);

    // Spawn producer
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            tx.send(format!("Message {}", i)).await.unwrap();
        }
    });

    // Consumer in main task
    let consumer = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Received: {}", message);
        }
    });

    let _ = tokio::join!(producer, consumer);
}
```

### Broadcast for Multiple Consumers
```rust
use tokio::sync::broadcast;

async fn broadcast_pattern() {
    let (tx, _rx) = broadcast::channel(16);

    // Spawn multiple consumers
    let mut consumers = Vec::new();
    for i in 0..3 {
        let mut consumer_rx = tx.subscribe();
        let consumer = tokio::spawn(async move {
            while let Ok(msg) = consumer_rx.recv().await {
                println!("Consumer {} received: {}", i, msg);
            }
        });
        consumers.push(consumer);
    }

    // Producer
    for i in 0..5 {
        tx.send(format!("Broadcast message {}", i)).unwrap();
    }

    // Wait for all consumers
    for consumer in consumers {
        consumer.await.unwrap();
    }
}
```

## Stream Processing

### Using async-stream
```rust
use async_stream::stream;
use futures::pin_mut;
use futures::stream::StreamExt;

fn number_stream() -> impl futures::Stream<Item = i32> {
    stream! {
        for i in 0..10 {
            yield i;
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }
}

async fn process_stream() {
    let s = number_stream();
    pin_mut!(s);

    while let Some(value) = s.next().await {
        println!("Streamed value: {}", value);
    }
}
```

### Buffering and Batching
```rust
use futures::stream::{self, StreamExt};

async fn batch_processing() {
    let items = stream::iter(0..100);

    items
        .chunks(10)
        .for_each(|batch| async move {
            process_batch(batch).await;
        })
        .await;
}

async fn process_batch(batch: Vec<i32>) {
    println!("Processing batch of {} items", batch.len());
    // Batch processing logic
}
```

## Resource Management

### Connection Pooling
```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

pub struct ConnectionPool {
    semaphore: Arc<Semaphore>,
    max_connections: usize,
}

impl ConnectionPool {
    pub fn new(max_connections: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_connections)),
            max_connections,
        }
    }

    pub async fn acquire(&self) -> Result<PooledConnection> {
        let permit = self.semaphore.acquire().await?;
        Ok(PooledConnection {
            _permit: permit,
            connection: create_connection().await?,
        })
    }
}
```

### Graceful Shutdown
```rust
use tokio::signal;
use tokio::sync::broadcast;

async fn graceful_shutdown() {
    let (shutdown_tx, _) = broadcast::channel::<()>(1);

    // Spawn shutdown signal handler
    let shutdown_tx_clone = shutdown_tx.clone();
    tokio::spawn(async move {
        signal::ctrl_c().await.expect("Failed to listen for ctrl+c");
        println!("Shutdown signal received");
        let _ = shutdown_tx_clone.send(());
    });

    // Spawn worker tasks with shutdown signal
    let mut tasks = Vec::new();
    for i in 0..3 {
        let mut shutdown_rx = shutdown_tx.subscribe();
        let task = tokio::spawn(async move {
            loop {
                select! {
                    _ = shutdown_rx.recv() => {
                        println!("Worker {} shutting down", i);
                        break;
                    }
                    _ = work() => {
                        // Continue working
                    }
                }
            }
        });
        tasks.push(task);
    }

    // Wait for all tasks to complete
    for task in tasks {
        task.await.unwrap();
    }
}
```

## Performance Optimization

### Avoid Blocking the Runtime
```rust
// Bad: blocking operation on async thread
async fn bad_example() {
    let result = std::thread::sleep(Duration::from_secs(1)); // DON'T DO THIS
}

// Good: use spawn_blocking for CPU-intensive work
async fn good_example() {
    let result = tokio::task::spawn_blocking(|| {
        // CPU-intensive work or blocking operations
        expensive_computation()
    }).await?;
}
```

### Task Spawning Strategy
```rust
// For CPU-bound tasks
async fn cpu_bound_work() {
    let handles: Vec<_> = (0..num_cpus::get())
        .map(|_| {
            tokio::task::spawn_blocking(|| {
                // CPU-intensive work
                heavy_computation()
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }
}

// For I/O-bound tasks
async fn io_bound_work() {
    let handles: Vec<_> = (0..100)
        .map(|i| {
            tokio::spawn(async move {
                // I/O operations
                fetch_data_from_api(i).await
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }
}
```

## Testing Async Code

### Using tokio::test
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_function() {
        let result = async_operation().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_timeout() {
        let result = tokio::time::timeout(
            Duration::from_millis(100),
            slow_operation()
        ).await;

        assert!(result.is_err()); // Should timeout
    }
}
```

## Common Pitfalls

1. **Blocking the runtime**: Never use blocking operations in async context
2. **Creating too many tasks**: Consider task pooling for high-frequency spawning
3. **Not handling backpressure**: Use bounded channels and flow control
4. **Ignoring cancellation**: Always handle cancellation tokens
5. **Memory leaks**: Ensure proper cleanup of resources and tasks
6. **Deadlocks**: Be careful with multiple locks and async boundaries