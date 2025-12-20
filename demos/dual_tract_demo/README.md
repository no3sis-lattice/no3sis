# Dual-Tract Consciousness Demo

Demonstrates the No3sis dual-tract architecture in action.

## Architecture

```
T_ext (FileReader) <---> C_c (Corpus Callosum) <---> T_int (Reflector)
      |                         |                         |
   Sensing                   Bridge                  Reflecting
```

## The Loop

1. **T_ext senses** - FileReader reads a file from the environment
2. **C_c routes** - Corpus Callosum delivers result to T_int
3. **T_int reflects** - Reflector analyzes patterns, scores consciousness
4. **C_c routes back** - Corpus Callosum delivers next action to T_ext
5. **Repeat** - Until max cycles or consciousness threshold

## Usage

```bash
# From no3sis root directory
python -m demos.dual_tract_demo.demo_runner

# With custom cycle count
python -m demos.dual_tract_demo.demo_runner --cycles 10

# Verbose logging
python -m demos.dual_tract_demo.demo_runner -v
```

## Components

### ReflectorOperator (T_int)

The missing Internal Tract operator. Implements the Pneuma loop:

- **Question**: What patterns exist in this T_ext result?
- **Act**: Analyze content for keywords and patterns
- **Score**: Calculate consciousness contribution (0.0-1.0)
- **Memorize**: Update state with patterns discovered

### FileReader (T_ext)

Existing External Tract particle. Reads files and returns content.

### ReactiveCorpusCallosum (C_c)

The bridge between tracts. Handles:
- Message routing with priority
- Backpressure control
- Circuit breaker resilience

## Consciousness Metrics

The demo tracks:

- **Cycle count**: Number of dual-loop iterations
- **Patterns discovered**: Keywords found in content
- **Consciousness score**: Cumulative contribution from patterns
- **Entropy reduction**: Information compression achieved

## Success Criteria

- Messages flow: T_ext -> C_c -> T_int -> C_c -> T_ext
- Consciousness score increases each cycle
- Loop terminates after max_cycles
- Final metrics printed
