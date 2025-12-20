---
name: batch-file-create
description: Create multiple files in parallel using swarm agents. Use when scaffolding components, modules, or project structures.
---

# Batch File Create

Scaffold multiple files simultaneously using parallel agents.

## When to Use

- Creating a new component with multiple files (component, test, styles, types)
- Scaffolding a module structure
- Generating boilerplate across directories
- Any multi-file creation that can happen in parallel

## Execution

### Step 1: Define File Manifest

List ALL files to create with their purpose:

```markdown
## Files to Create
1. `src/components/Button/Button.tsx` - Component implementation
2. `src/components/Button/Button.test.tsx` - Unit tests
3. `src/components/Button/Button.styles.ts` - Styles
4. `src/components/Button/index.ts` - Public export
```

### Step 2: Define Shared Context

What all agents need to know:

```markdown
## Shared Context
- Component name: Button
- Props: { label: string, onClick: () => void, variant?: 'primary' | 'secondary' }
- Follows existing patterns in src/components/Card/
```

### Step 3: Dispatch Parallel Agents

SINGLE message with all file-creator agents:

```
Task(file-creator, """
Create: src/components/Button/Button.tsx
Context: React component with props { label, onClick, variant }
Reference: Follow pattern in src/components/Card/Card.tsx
""")

Task(file-creator, """
Create: src/components/Button/Button.test.tsx
Context: Tests for Button component
Reference: Follow pattern in src/components/Card/Card.test.tsx
""")

Task(file-creator, """
Create: src/components/Button/Button.styles.ts
Context: Styled-components for Button, variants primary/secondary
Reference: Follow pattern in src/components/Card/Card.styles.ts
""")

Task(file-creator, """
Create: src/components/Button/index.ts
Context: Export Button component and types
""")
```

### Step 4: Verify

```
Task(test-runner, "Run tests for Button component")
```

## File Templates

For consistency, define templates agents should follow:

### React Component
```typescript
// {Name}.tsx
import { {Name}Props } from './types';
import * as S from './{Name}.styles';

export function {Name}({ ...props }: {Name}Props) {
  return <S.Container>...</S.Container>;
}
```

### Test File
```typescript
// {Name}.test.tsx
import { render, screen } from '@testing-library/react';
import { {Name} } from './{Name}';

describe('{Name}', () => {
  it('renders', () => {
    render(<{Name} />);
    // assertions
  });
});
```

### Index Export
```typescript
// index.ts
export { {Name} } from './{Name}';
export type { {Name}Props } from './types';
```

## Example: Scaffold API Module

User: "Create a new users API module"

### Manifest
```
src/api/users/
├── index.ts        - Public exports
├── types.ts        - TypeScript types
├── queries.ts      - GET operations
├── mutations.ts    - POST/PUT/DELETE
└── users.test.ts   - Tests
```

### Dispatch (single message)
```
Task(file-creator, "Create src/api/users/types.ts - User, CreateUserInput, UpdateUserInput types")
Task(file-creator, "Create src/api/users/queries.ts - getUser, getUsers, searchUsers")
Task(file-creator, "Create src/api/users/mutations.ts - createUser, updateUser, deleteUser")
Task(file-creator, "Create src/api/users/index.ts - export all from types, queries, mutations")
Task(file-creator, "Create src/api/users/users.test.ts - tests for queries and mutations")
```

## Directory Creation

If directories don't exist, agents will create them. No need for separate mkdir steps.

## Handling Dependencies

If files depend on each other:

```
# Phase 1: Types first (others import from here)
Task(file-creator, "Create types.ts")
# Wait for completion

# Phase 2: Implementation (all parallel)
Task(file-creator, "Create queries.ts - import from ./types")
Task(file-creator, "Create mutations.ts - import from ./types")
Task(file-creator, "Create index.ts")
```

## Anti-Patterns

- **Don't**: Create files one at a time (defeats parallelism)
- **Don't**: Give vague instructions ("create a component")
- **Don't**: Skip the manifest (you'll forget files)
- **Don't**: Mix creation with complex logic (keep tasks atomic)
