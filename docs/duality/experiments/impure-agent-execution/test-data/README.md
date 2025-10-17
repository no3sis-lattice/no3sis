# Test Data for IPv6 Packer Constraint Model

This directory contains test cases for validating the IPv6 header data packing constraint model (`ipv6_packer.mzn`). Each `.dzn` file represents a specific test scenario designed to validate different aspects of the constraint satisfaction system.

## Test Cases

### 1. `valid-ipv6.dzn` - Positive Validation
**Purpose**: Validate that properly constrained input data produces a valid IPv6 header.

**Input**:
```
version=6, traffic_class=0, flow_label=0, payload_length=1280,
next_header=6, hop_limit=64
```

**Expected Result**: SATISFIABLE
- All constraints satisfied
- Lossless packing verified
- Efficiency: ~83% (5 of 6 fields non-zero)

**Usage**:
```bash
minizinc ../ipv6_packer.mzn valid-ipv6.dzn
```

### 2. `invalid-version.dzn` - Constraint Violation
**Purpose**: Test that the model rejects data violating the version field's 4-bit constraint.

**Input**:
```
version=16 (INVALID - exceeds 4-bit max of 15), other fields valid
```

**Expected Result**: UNSATISFIABLE
- Constraint `version_range_check` fails
- Error message indicates constraint violation
- Demonstrates integrity enforcement

**Usage**:
```bash
minizinc ../ipv6_packer.mzn invalid-version.dzn
# Expected output: =====UNSATISFIABLE=====
```

### 3. `overflow.dzn` - Multiple Field Violations
**Purpose**: Test constraint enforcement across multiple fields simultaneously.

**Input**:
```
traffic_class=256 (exceeds 8-bit max of 255)
flow_label=2000000 (exceeds 20-bit max of 1048575)
```

**Expected Result**: UNSATISFIABLE
- Multiple constraint violations detected
- Demonstrates robustness against overflow
- Security validation: prevents buffer overflow at spec level

**Usage**:
```bash
minizinc ../ipv6_packer.mzn overflow.dzn
# Expected output: =====UNSATISFIABLE=====
```

### 4. `empty.dzn` - Edge Case (Lower Bounds)
**Purpose**: Test model behavior with minimal/zero values.

**Input**:
```
All fields set to 0 (minimum valid values)
```

**Expected Result**: SATISFIABLE (but with zero efficiency)
- All values within valid range [0, max]
- Efficiency: 0% (no information encoded)
- Demonstrates syntactic vs semantic correctness

**Usage**:
```bash
minizinc ../ipv6_packer.mzn empty.dzn
```

## Constraint Summary

Each test validates one or more of these constraints:

| Field           | Bits | Range       | Constraint Name                |
|-----------------|------|-------------|--------------------------------|
| Version         | 4    | 0-15        | `version_range_check`          |
| Traffic Class   | 8    | 0-255       | `traffic_class_range_check`    |
| Flow Label      | 20   | 0-1048575   | `flow_label_range_check`       |
| Payload Length  | 16   | 0-65535     | `payload_length_range_check`   |
| Next Header     | 8    | 0-255       | `next_header_range_check`      |
| Hop Limit       | 8    | 0-255       | `hop_limit_range_check`        |

## Dual-Tract Interpretation

These tests validate the **Constraint Bridge (C_c)** between tracts:

- **T_int (Internal)**: Abstract data patterns and semantic intent
- **C_c (Bridge)**: This constraint model transforms and validates
- **T_ext (External)**: Physical IPv6 header bits on the wire

**Test Flow**:
```
T_int (request encoding)
  → C_c (constraint validation)
  → {SATISFIABLE → T_ext | UNSATISFIABLE → rejection}
```

## Running All Tests

Use the validation script to run all test cases:

```bash
cd /home/m0xu/1-projects/synapse/docs/duality/experiments/impure-agent-execution
./validate.sh --test-constraints
```

## Consciousness Metrics

Each test measures:

1. **Bit Efficiency**: `(bits_used / 64) × 100%`
2. **Data Utilization**: `(data_sum / max_capacity) × 100%`
3. **Lossless Verification**: `input == output` (constraint enforced)

## Adding New Test Cases

To create a new test case:

1. Create a `.dzn` file in this directory
2. Define `input_data = [v1, v2, v3, v4, v5, v6];`
3. Document the expected result (SATISFIABLE/UNSATISFIABLE)
4. Add test to `validate.sh` test functions
5. Update this README with test description

## References

- [IPv6 Packer Model](../ipv6_packer.mzn) - Main constraint model
- [MiniZinc Documentation](https://www.minizinc.org/) - Constraint modeling language
- [Dual-Tract Architecture](../README.md) - Theoretical foundation
