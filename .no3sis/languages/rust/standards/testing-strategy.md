# Rust Testing Strategy

Comprehensive testing approach for robust, maintainable Rust applications.

## Test Organization

### Test Module Structure
```rust
// src/lib.rs or src/main.rs
pub mod user_service;
pub mod database;

#[cfg(test)]
mod tests {
    use super::*;

    // Integration tests for the entire module
    #[test]
    fn test_end_to_end_workflow() {
        // Test complete workflows
    }
}

// src/user_service.rs
pub struct UserService { ... }

impl UserService {
    pub fn create_user(&self, email: &str) -> Result<User, UserError> { ... }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_user_success() {
        let service = UserService::new();
        let result = service.create_user("test@example.com");
        assert!(result.is_ok());
    }

    #[test]
    fn test_create_user_invalid_email() {
        let service = UserService::new();
        let result = service.create_user("invalid-email");
        assert!(matches!(result, Err(UserError::InvalidEmail)));
    }
}
```

### Integration Tests
```
tests/
├── common/
│   └── mod.rs           # Common test utilities
├── integration_test.rs  # Main integration tests
├── api_tests.rs        # API endpoint tests
└── database_tests.rs   # Database integration tests
```

```rust
// tests/common/mod.rs
use std::sync::Once;

static INIT: Once = Once::new();

pub fn setup() {
    INIT.call_once(|| {
        // Initialize test environment
        env_logger::init();
    });
}

pub fn create_test_database() -> TestDatabase {
    // Setup test database
}

// tests/integration_test.rs
mod common;

use common::*;

#[test]
fn test_user_registration_flow() {
    setup();
    let db = create_test_database();
    // Integration test logic
}
```

## Unit Testing Patterns

### Testing Pure Functions
```rust
pub fn calculate_fibonacci(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => calculate_fibonacci(n - 1) + calculate_fibonacci(n - 2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci_base_cases() {
        assert_eq!(calculate_fibonacci(0), 0);
        assert_eq!(calculate_fibonacci(1), 1);
    }

    #[test]
    fn test_fibonacci_sequence() {
        assert_eq!(calculate_fibonacci(2), 1);
        assert_eq!(calculate_fibonacci(3), 2);
        assert_eq!(calculate_fibonacci(4), 3);
        assert_eq!(calculate_fibonacci(5), 5);
    }

    #[test]
    fn test_fibonacci_larger_numbers() {
        assert_eq!(calculate_fibonacci(10), 55);
        assert_eq!(calculate_fibonacci(15), 610);
    }
}
```

### Testing with Result Types
```rust
pub fn parse_age(input: &str) -> Result<u32, ParseError> {
    let age: u32 = input.parse()
        .map_err(|_| ParseError::InvalidNumber)?;

    if age > 150 {
        return Err(ParseError::UnrealisticAge);
    }

    Ok(age)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_valid_age() {
        assert_eq!(parse_age("25").unwrap(), 25);
        assert_eq!(parse_age("0").unwrap(), 0);
        assert_eq!(parse_age("150").unwrap(), 150);
    }

    #[test]
    fn test_parse_invalid_number() {
        assert!(matches!(parse_age("abc"), Err(ParseError::InvalidNumber)));
        assert!(matches!(parse_age("25.5"), Err(ParseError::InvalidNumber)));
    }

    #[test]
    fn test_parse_unrealistic_age() {
        assert!(matches!(parse_age("200"), Err(ParseError::UnrealisticAge)));
    }
}
```

## Async Testing

### Testing Async Functions
```rust
use tokio::test;

pub async fn fetch_user_data(user_id: u64) -> Result<UserData, ApiError> {
    // Async implementation
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_fetch_user_data_success() {
        let result = fetch_user_data(123).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_fetch_user_data_not_found() {
        let result = fetch_user_data(99999).await;
        assert!(matches!(result, Err(ApiError::UserNotFound)));
    }

    #[tokio::test]
    async fn test_concurrent_requests() {
        let futures = (1..=10).map(|id| fetch_user_data(id));
        let results = futures::future::join_all(futures).await;

        assert_eq!(results.len(), 10);
        assert!(results.iter().all(|r| r.is_ok()));
    }
}
```

### Testing with Timeouts
```rust
use tokio::time::{timeout, Duration};

#[tokio::test]
async fn test_operation_completes_in_time() {
    let result = timeout(
        Duration::from_secs(1),
        slow_operation()
    ).await;

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_operation_times_out() {
    let result = timeout(
        Duration::from_millis(100),
        very_slow_operation()
    ).await;

    assert!(result.is_err());
}
```

## Mocking and Test Doubles

### Trait-Based Mocking
```rust
use async_trait::async_trait;

#[async_trait]
pub trait UserRepository {
    async fn find_user(&self, id: u64) -> Result<User, DatabaseError>;
    async fn save_user(&self, user: &User) -> Result<(), DatabaseError>;
}

pub struct DatabaseUserRepository { ... }

#[async_trait]
impl UserRepository for DatabaseUserRepository {
    async fn find_user(&self, id: u64) -> Result<User, DatabaseError> {
        // Real database implementation
    }

    async fn save_user(&self, user: &User) -> Result<(), DatabaseError> {
        // Real database implementation
    }
}

// Test implementation
pub struct MockUserRepository {
    users: HashMap<u64, User>,
    should_fail: bool,
}

impl MockUserRepository {
    pub fn new() -> Self {
        Self {
            users: HashMap::new(),
            should_fail: false,
        }
    }

    pub fn with_user(mut self, user: User) -> Self {
        self.users.insert(user.id, user);
        self
    }

    pub fn set_should_fail(mut self, should_fail: bool) -> Self {
        self.should_fail = should_fail;
        self
    }
}

#[async_trait]
impl UserRepository for MockUserRepository {
    async fn find_user(&self, id: u64) -> Result<User, DatabaseError> {
        if self.should_fail {
            return Err(DatabaseError::ConnectionFailed);
        }

        self.users.get(&id)
            .cloned()
            .ok_or(DatabaseError::UserNotFound)
    }

    async fn save_user(&self, user: &User) -> Result<(), DatabaseError> {
        if self.should_fail {
            return Err(DatabaseError::ConnectionFailed);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_user_service_with_mock() {
        let user = User::new(1, "test@example.com");
        let repo = MockUserRepository::new().with_user(user.clone());
        let service = UserService::new(Box::new(repo));

        let result = service.get_user(1).await;
        assert_eq!(result.unwrap(), user);
    }

    #[tokio::test]
    async fn test_user_service_handles_repository_failure() {
        let repo = MockUserRepository::new().set_should_fail(true);
        let service = UserService::new(Box::new(repo));

        let result = service.get_user(1).await;
        assert!(matches!(result, Err(ServiceError::DatabaseError(_))));
    }
}
```

## Property-Based Testing

### Using quickcheck
```rust
use quickcheck::{quickcheck, TestResult};

fn reverse_twice<T: Clone>(xs: Vec<T>) -> Vec<T> {
    let mut reversed = xs.clone();
    reversed.reverse();
    reversed.reverse();
    reversed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[quickcheck]
    fn prop_reverse_twice_is_identity(xs: Vec<i32>) -> bool {
        reverse_twice(xs.clone()) == xs
    }

    #[quickcheck]
    fn prop_parse_age_valid_range(age: u8) -> TestResult {
        if age > 150 {
            return TestResult::discard();
        }

        let age_str = age.to_string();
        let parsed = parse_age(&age_str);

        TestResult::from_bool(parsed == Ok(age as u32))
    }
}
```

### Using proptest
```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_string_roundtrip(s in "\\PC*") {
        let encoded = encode_string(&s);
        let decoded = decode_string(&encoded).unwrap();
        prop_assert_eq!(s, decoded);
    }

    #[test]
    fn test_positive_numbers_stay_positive(n in 1u32..1000) {
        prop_assert!(process_positive_number(n) > 0);
    }
}
```

## Benchmark Testing

### Using criterion
```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci_benchmark(c: &mut Criterion) {
    c.bench_function("fibonacci 20", |b| {
        b.iter(|| calculate_fibonacci(black_box(20)))
    });
}

fn string_processing_benchmark(c: &mut Criterion) {
    let data = "long string data for processing".repeat(1000);

    c.bench_function("string processing", |b| {
        b.iter(|| process_string(black_box(&data)))
    });
}

criterion_group!(benches, fibonacci_benchmark, string_processing_benchmark);
criterion_main!(benches);
```

## Test Data Management

### Fixture Generation
```rust
pub struct UserFixture {
    pub id: u64,
    pub email: String,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl UserFixture {
    pub fn new() -> Self {
        Self {
            id: 1,
            email: "test@example.com".to_string(),
            name: "Test User".to_string(),
            created_at: Utc::now(),
        }
    }

    pub fn with_id(mut self, id: u64) -> Self {
        self.id = id;
        self
    }

    pub fn with_email(mut self, email: &str) -> Self {
        self.email = email.to_string();
        self
    }

    pub fn build(self) -> User {
        User {
            id: self.id,
            email: self.email,
            name: self.name,
            created_at: self.created_at,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_with_fixture() {
        let user = UserFixture::new()
            .with_id(42)
            .with_email("custom@example.com")
            .build();

        assert_eq!(user.id, 42);
        assert_eq!(user.email, "custom@example.com");
    }
}
```

## Test Configuration

### Cargo.toml Configuration
```toml
[dev-dependencies]
tokio-test = "0.4"
criterion = "0.5"
quickcheck = "1.0"
proptest = "1.0"
mockall = "0.11"

[[bench]]
name = "my_benchmark"
harness = false

[package.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
```

## Testing Best Practices

### 1. Test Organization
- Group related tests in modules
- Use descriptive test names that explain the scenario
- Follow the Arrange-Act-Assert pattern
- Keep tests focused and independent

### 2. Coverage Goals
- Aim for high test coverage but focus on critical paths
- Test error conditions and edge cases
- Include both positive and negative test cases
- Test public APIs thoroughly

### 3. Test Data
- Use fixtures for complex test data
- Make test data obvious and minimal
- Avoid shared mutable state between tests
- Use builder patterns for flexible test data creation

### 4. Async Testing
- Always use `#[tokio::test]` for async tests
- Test timeout scenarios explicitly
- Test concurrent behavior when relevant
- Use appropriate runtime configurations

### 5. Integration Tests
- Test real workflows end-to-end
- Use separate test databases or environments
- Test external integrations with appropriate isolation
- Document test setup requirements

### 6. Performance Testing
- Include benchmarks for performance-critical code
- Test with realistic data sizes
- Monitor for performance regressions
- Document performance expectations