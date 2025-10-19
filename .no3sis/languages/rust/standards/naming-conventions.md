# Rust Naming Conventions

Comprehensive naming standards for consistent, readable Rust code following community best practices.

## General Principles

- Use **snake_case** for variables, functions, modules, and macros
- Use **PascalCase** for types, traits, and enum variants
- Use **SCREAMING_SNAKE_CASE** for constants and statics
- Use descriptive names that communicate intent
- Prefer clarity over brevity

## Variables and Functions

### Variables
```rust
// Good
let user_count = 10;
let database_connection = establish_connection();
let is_authenticated = check_user_status();

// Avoid
let cnt = 10;
let db = establish_connection();
let auth = check_user_status();
```

### Functions
```rust
// Good
fn calculate_total_price(items: &[Item], tax_rate: f64) -> f64 { ... }
fn validate_email_format(email: &str) -> bool { ... }
fn send_notification_to_user(user_id: UserId, message: &str) { ... }

// Avoid
fn calc(items: &[Item], rate: f64) -> f64 { ... }
fn check_email(email: &str) -> bool { ... }
fn notify(user_id: UserId, msg: &str) { ... }
```

### Boolean Functions and Variables
```rust
// Predicates should start with is_, has_, can_, should_
fn is_valid_user(user: &User) -> bool { ... }
fn has_permission(user: &User, resource: &Resource) -> bool { ... }
fn can_access_file(path: &Path) -> bool { ... }
fn should_retry_request(attempt_count: usize) -> bool { ... }

let is_connected = check_connection();
let has_data = !buffer.is_empty();
let can_proceed = validate_preconditions();
```

## Types and Traits

### Structs
```rust
// Good
struct UserAccount {
    user_id: UserId,
    email_address: String,
    created_at: DateTime<Utc>,
    last_login: Option<DateTime<Utc>>,
}

struct DatabaseConnection {
    connection_pool: Pool<ConnectionManager>,
    timeout_duration: Duration,
}

// Avoid generic names
struct Data { ... }  // Too generic
struct Manager { ... }  // Too vague
```

### Enums
```rust
// Good
enum PaymentMethod {
    CreditCard { number: String, expiry: String },
    PayPal { email: String },
    BankTransfer { account_number: String, routing_number: String },
}

enum HttpStatus {
    Ok,
    NotFound,
    InternalServerError,
    BadRequest,
}

// Error types should end with Error
enum ValidationError {
    InvalidEmail,
    PasswordTooShort,
    UsernameExists,
}
```

### Traits
```rust
// Good - traits describe capabilities or behaviors
trait Serializable {
    fn serialize(&self) -> Vec<u8>;
    fn deserialize(data: &[u8]) -> Result<Self, SerializationError>;
}

trait Cacheable {
    fn cache_key(&self) -> String;
    fn cache_duration(&self) -> Duration;
}

// For conversion traits, follow standard patterns
trait FromConfigFile {
    fn from_config_file(path: &Path) -> Result<Self, ConfigError>;
}
```

## Modules and Crates

### Module Names
```rust
// Good
mod user_authentication;
mod database_operations;
mod payment_processing;
mod error_handling;

// Avoid
mod utils;  // Too generic
mod stuff;  // Meaningless
mod misc;   // Non-descriptive
```

### Crate Names
```rust
// Good crate names (use kebab-case in Cargo.toml)
my-project-core
user-authentication-service
database-migration-tool
web-api-client

// In Rust code, these become
use my_project_core::UserManager;
use user_authentication_service::AuthToken;
```

## Constants and Statics

```rust
// Good
const MAX_RETRY_ATTEMPTS: usize = 3;
const DEFAULT_TIMEOUT_SECONDS: u64 = 30;
const API_VERSION: &str = "v1.2.0";

static GLOBAL_CONFIG: OnceLock<Configuration> = OnceLock::new();
static DATABASE_POOL: OnceLock<Pool> = OnceLock::new();

// Environment variable names
const ENV_DATABASE_URL: &str = "DATABASE_URL";
const ENV_LOG_LEVEL: &str = "LOG_LEVEL";
```

## Generic Type Parameters

```rust
// Single letters for simple generics
struct Container<T> {
    items: Vec<T>,
}

// Descriptive names for complex generics
struct EventProcessor<Event, Handler, Error>
where
    Handler: Fn(Event) -> Result<(), Error>,
{
    handler: Handler,
    _phantom: PhantomData<(Event, Error)>,
}

// Common patterns
impl<T, E> Result<T, E> { ... }  // T for success type, E for error type
impl<K, V> HashMap<K, V> { ... }  // K for key, V for value
impl<I> Iterator for I { ... }    // I for iterator type
```

## Lifetime Parameters

```rust
// Use descriptive names for complex lifetimes
struct Parser<'input, 'config> {
    input: &'input str,
    config: &'config ParserConfig,
}

// Common patterns
fn process_data<'a>(data: &'a str) -> &'a str { ... }
fn merge_configs<'a, 'b>(
    primary: &'a Config,
    secondary: &'b Config,
) -> MergedConfig<'a, 'b> { ... }
```

## Method Names

### Constructors
```rust
impl UserAccount {
    // Primary constructor
    fn new(email: String, password: String) -> Self { ... }

    // Alternative constructors
    fn from_existing_user(user_id: UserId) -> Result<Self, Error> { ... }
    fn with_default_settings(email: String) -> Self { ... }
    fn from_json(json_str: &str) -> Result<Self, ParseError> { ... }
}
```

### Getters and Setters
```rust
impl UserAccount {
    // Getters - no "get_" prefix
    fn email(&self) -> &str { &self.email_address }
    fn user_id(&self) -> UserId { self.user_id }
    fn created_at(&self) -> DateTime<Utc> { self.created_at }

    // Setters - clear mutation intent
    fn set_email(&mut self, email: String) { ... }
    fn update_last_login(&mut self, timestamp: DateTime<Utc>) { ... }

    // Consuming methods
    fn into_summary(self) -> UserSummary { ... }
    fn into_json(self) -> String { ... }
}
```

### Actions and Commands
```rust
impl DatabaseManager {
    // Actions should be verbs
    fn connect(&mut self) -> Result<(), ConnectionError> { ... }
    fn execute_query(&self, query: &str) -> QueryResult { ... }
    fn migrate_schema(&self, version: SchemaVersion) -> MigrationResult { ... }

    // State changes
    fn mark_as_ready(&mut self) { ... }
    fn reset_connection(&mut self) { ... }
    fn shutdown(&mut self) { ... }
}
```

## File and Directory Names

```
src/
├── main.rs                    # Application entry point
├── lib.rs                     # Library root
├── user_management/           # Module directory
│   ├── mod.rs                # Module declaration
│   ├── user_account.rs       # Specific functionality
│   ├── authentication.rs    # Related functionality
│   └── permissions.rs       # Related functionality
├── database/
│   ├── mod.rs
│   ├── connection_pool.rs
│   ├── migration_runner.rs
│   └── query_builder.rs
└── error_types.rs            # Standalone module
```

## API Design Patterns

### Builder Pattern
```rust
pub struct HttpClientBuilder {
    timeout: Option<Duration>,
    user_agent: Option<String>,
    max_retries: Option<usize>,
}

impl HttpClientBuilder {
    pub fn new() -> Self { ... }
    pub fn with_timeout(mut self, timeout: Duration) -> Self { ... }
    pub fn with_user_agent(mut self, user_agent: String) -> Self { ... }
    pub fn with_max_retries(mut self, retries: usize) -> Self { ... }
    pub fn build(self) -> HttpClient { ... }
}
```

### Type State Pattern
```rust
struct ConnectionBuilder<State> {
    config: ConnectionConfig,
    _state: PhantomData<State>,
}

struct Configured;
struct Connected;

impl ConnectionBuilder<()> {
    fn new() -> ConnectionBuilder<()> { ... }
    fn configure(self, config: Config) -> ConnectionBuilder<Configured> { ... }
}

impl ConnectionBuilder<Configured> {
    fn connect(self) -> Result<ConnectionBuilder<Connected>, Error> { ... }
}
```

## Documentation Standards

```rust
/// Calculates the total price including tax for a collection of items.
///
/// # Arguments
///
/// * `items` - A slice of items to calculate the total for
/// * `tax_rate` - The tax rate as a decimal (e.g., 0.08 for 8%)
///
/// # Returns
///
/// The total price including tax as a floating-point number
///
/// # Examples
///
/// ```
/// use my_crate::calculate_total_with_tax;
///
/// let items = vec![Item::new("Widget", 10.00), Item::new("Gadget", 15.00)];
/// let total = calculate_total_with_tax(&items, 0.08);
/// assert_eq!(total, 27.00);
/// ```
///
/// # Panics
///
/// This function will panic if the tax rate is negative.
pub fn calculate_total_with_tax(items: &[Item], tax_rate: f64) -> f64 {
    assert!(tax_rate >= 0.0, "Tax rate cannot be negative");
    // Implementation...
}
```

## Anti-Patterns to Avoid

1. **Hungarian notation**: `strName`, `intCount` - not idiomatic in Rust
2. **Generic suffixes**: `data`, `info`, `manager` without context
3. **Abbreviations**: `usr` instead of `user`, `cfg` instead of `config`
4. **Misleading names**: Functions that don't match their behavior
5. **Inconsistent naming**: Mixing conventions within the same codebase
6. **Overly long names**: `calculate_the_total_price_for_all_items_including_tax`