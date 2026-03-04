# RV64M Support in zigz

## Overview

zigz has **complete RV64M (multiply/divide extension)** support, including all integer multiplication, division, and remainder operations. The RV64M extension is one of the most widely used RISC-V extensions, as most non-trivial programs require multiplication and division.

## RV64M Features

### 1. 64-bit Operations

All operations work on full 64-bit operands:

#### Multiplication
- **MUL** - Multiply (lower 64 bits of result)
- **MULH** - Multiply High (signed × signed, upper 64 bits)
- **MULHSU** - Multiply High (signed × unsigned, upper 64 bits)
- **MULHU** - Multiply High (unsigned × unsigned, upper 64 bits)

#### Division and Remainder
- **DIV** - Signed division
- **DIVU** - Unsigned division
- **REM** - Signed remainder
- **REMU** - Unsigned remainder

### 2. 32-bit Word Operations

Word operations (*W suffix) operate on lower 32 bits and sign-extend:

- **MULW** - Multiply Word (lower 32 bits, sign-extended)
- **DIVW** - Signed division word
- **DIVUW** - Unsigned division word
- **REMW** - Signed remainder word
- **REMUW** - Unsigned remainder word

## Instruction Encoding

RV64M instructions use the **OP** (0b0110011) and **OP_32** (0b0111011) opcodes with **funct7 = 0b0000001** to distinguish them from base RV64I instructions.

| Instruction | Opcode | funct3 | funct7 |
|-------------|--------|--------|--------|
| MUL | OP | 0b000 | 0b0000001 |
| MULH | OP | 0b001 | 0b0000001 |
| MULHSU | OP | 0b010 | 0b0000001 |
| MULHU | OP | 0b011 | 0b0000001 |
| DIV | OP | 0b100 | 0b0000001 |
| DIVU | OP | 0b101 | 0b0000001 |
| REM | OP | 0b110 | 0b0000001 |
| REMU | OP | 0b111 | 0b0000001 |
| MULW | OP_32 | 0b000 | 0b0000001 |
| DIVW | OP_32 | 0b100 | 0b0000001 |
| DIVUW | OP_32 | 0b101 | 0b0000001 |
| REMW | OP_32 | 0b110 | 0b0000001 |
| REMUW | OP_32 | 0b111 | 0b0000001 |

## Semantics

### Multiplication Semantics

**MUL**: Returns the lower 64 bits of the product.
```
MUL rd, rs1, rs2
rd = (rs1 * rs2)[63:0]
```

**MULH/MULHSU/MULHU**: Return the upper 64 bits of a 128-bit product.
```
MULH rd, rs1, rs2   # Signed × Signed
rd = (signed(rs1) * signed(rs2))[127:64]

MULHSU rd, rs1, rs2  # Signed × Unsigned
rd = (signed(rs1) * unsigned(rs2))[127:64]

MULHU rd, rs1, rs2   # Unsigned × Unsigned
rd = (unsigned(rs1) * unsigned(rs2))[127:64]
```

**MULW**: Multiplies lower 32 bits and sign-extends result.
```
MULW rd, rs1, rs2
result32 = rs1[31:0] * rs2[31:0]
rd = sign_extend(result32)
```

### Division and Remainder Semantics

**DIV/DIVU**: Integer division (truncated toward zero).
```
DIV rd, rs1, rs2    # Signed division
DIVU rd, rs1, rs2   # Unsigned division
```

**REM/REMU**: Remainder after division.
```
REM rd, rs1, rs2    # Signed remainder
REMU rd, rs1, rs2   # Unsigned remainder
```

#### Special Cases

**Division by Zero**:
- DIV: Returns -1 (all bits set)
- DIVU: Returns 2^64-1 (all bits set)
- REM/REMU: Returns dividend (unchanged)

**Overflow** (INT64_MIN / -1):
- DIV: Returns dividend (INT64_MIN)
- REM: Returns 0

These behaviors match the RISC-V specification exactly.

## Implementation

### VM State Machine

`src/vm/state.zig` implements RV64M in `executeOP()` and `executeOP32()`:

**64-bit Operations** (`executeOP`):
- Check `funct7 == 0b0000001` to identify RV64M instructions
- Use Zig's 128-bit integer types (i128/u128) for high multiply operations
- Handle division-by-zero and overflow cases per spec

**Word Operations** (`executeOP32`):
- Truncate operands to 32 bits
- Perform 32-bit operation
- Sign-extend result to 64 bits

### Key Implementation Details

**High Multiply (MULH/MULHSU/MULHU)**:
```zig
// Example: MULH (signed × signed)
const a: i128 = @as(i64, @bitCast(rs1_val));
const b: i128 = @as(i64, @bitCast(rs2_val));
const product: i128 = a *% b;
result = @as(u64, @bitCast(@as(i64, @truncate(product >> 64))));
```

**Division by Zero**:
```zig
if (b == 0) {
    break :blk @as(u64, @bitCast(@as(i64, -1))); // DIV: return -1
}
```

**Overflow Handling**:
```zig
if (a == std.math.minInt(i64) and b == -1) {
    break :blk @bitCast(a); // DIV: return dividend
}
```

## Testing

### Unit Tests

**VM Execution** (`tests/test_rv64m.zig`):
- ✅ MUL (basic multiplication)
- ✅ MULH (signed × signed high multiply)
- ✅ MULHU (unsigned × unsigned high multiply)
- ✅ DIV (signed division)
- ✅ DIV by zero (returns -1)
- ✅ DIVU (unsigned division)
- ✅ REM (signed remainder)
- ✅ REMU (unsigned remainder)
- ✅ MULW (word multiply with sign extension)
- ✅ MULW overflow (sign extension of negative results)
- ✅ DIVW (signed word division)
- ✅ DIVUW (unsigned word division)
- ✅ REMW (signed word remainder)
- ✅ REMUW (unsigned word remainder)
- ✅ Negative number multiplication
- ✅ Large number multiplication (testing high bits)

### Running Tests

```bash
# RV64M multiply/divide tests
zig build test-rv64m

# All tests including RV64M
zig build test-all
```

## Usage Examples

### Example 1: Basic Multiplication

```zig
// Multiply 6 × 7 = 42
LI x10, 6
LI x11, 7
MUL x12, x10, x11
// x12 = 42
```

### Example 2: High Multiply for Large Products

```zig
// Compute 2^32 × 2^32 = 2^64
LI x10, 0x100000000  // 2^32
LI x11, 0x100000000  // 2^32

MUL x12, x10, x11    // Lower 64 bits = 0
MULHU x13, x10, x11  // Upper 64 bits = 1

// Result: 0x10000000000000000 (2^64)
// x12 = 0x0000000000000000
// x13 = 0x0000000000000001
```

### Example 3: Division and Remainder

```zig
// Divide 20 by 3
LI x10, 20
LI x11, 3

DIV x12, x10, x11    // x12 = 6 (quotient)
REM x13, x10, x11    // x13 = 2 (remainder)

// Verify: 6 × 3 + 2 = 20 ✓
```

### Example 4: Division by Zero Handling

```zig
// Test division by zero behavior
LI x10, 42
LI x11, 0

DIV x12, x10, x11    // x12 = 0xFFFFFFFFFFFFFFFF (-1)
REM x13, x10, x11    // x13 = 42 (dividend unchanged)
```

### Example 5: Word Multiplication with Overflow

```zig
// 32-bit multiplication with sign extension
LI x10, 0x7FFFFFFF   // Max positive 32-bit int
LI x11, 2

MULW x12, x10, x11   // 0x7FFFFFFF × 2 = 0xFFFFFFFE
// x12 = 0xFFFFFFFFFFFFFFFE (sign-extended negative)

// Compare with 64-bit multiply:
MUL x13, x10, x11    // 0x7FFFFFFF × 2 = 0xFFFFFFFE
// x13 = 0x00000000FFFFFFFE (positive 64-bit value)
```

## Performance Characteristics

### Operation Costs

In the zkVM context:
- **MUL**: Similar cost to ADD (single constraint)
- **MULH/MULHSU/MULHU**: Requires decomposition into 32-bit chunks
- **DIV/DIVU/REM/REMU**: More expensive (requires range checks and inverse computation)

### Optimization Strategies

1. **Prefer MUL over MULH**: Use only when high bits are needed
2. **Division is expensive**: Consider multiplication by inverse when possible
3. **Power-of-2 division**: Use shifts instead (SRL/SRA)
4. **Word operations**: Use *W variants when working with 32-bit values

## Why RV64M Is Essential

RV64M is considered **mandatory** for any practical RISC-V implementation:

1. **Ubiquitous use**: Most programs need multiplication/division
2. **Compiler dependency**: Modern compilers emit MUL/DIV instructions regularly
3. **Algorithm support**: Many algorithms require these operations (crypto, hashing, etc.)
4. **Standard library**: libc and other libraries depend on M extension

Unlike optional extensions (F/D for floating-point, A for atomics), RV64M is expected to be present in virtually all RISC-V implementations.

## Integration with zkVM

The zkVM prover handles RV64M operations through constraint generation:

1. **Multiplication**: Decomposed into limb-wise products with carry propagation
2. **Division**: Verified by computing quotient × divisor + remainder = dividend
3. **Range checks**: Ensure quotient and remainder are in valid ranges
4. **Special cases**: Division by zero and overflow handled with conditional constraints

The verifier checks these constraints without re-executing the operations.

## Differences from Other Extensions

| Feature | RV64I (Base) | RV64M (Multiply/Divide) |
|---------|--------------|-------------------------|
| Opcodes | OP/OP_32 | OP/OP_32 with funct7=0b0000001 |
| Operations | ADD, SUB, shifts, logical | MUL, DIV, REM |
| Constraint cost | Low | Medium (MUL) to High (DIV) |
| Compiler dependency | Required | Near-universal |

## Limitations

Current implementation:
- ✅ All RV64M instructions implemented
- ✅ Full specification compliance (division by zero, overflow)
- ✅ Comprehensive test coverage
- ⚠️ Division constraints in zkVM are more expensive than multiplication

Future optimizations:
- Optimize division constraint generation
- Add lookup tables for small divisors
- Implement Barrett reduction for modular arithmetic

## References

- [RISC-V Instruction Set Manual](https://riscv.org/technical/specifications/)
- [RV64M Extension Specification](https://riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf) (Chapter 7)
- [Zig Language Reference - 128-bit integers](https://ziglang.org/documentation/master/#Primitive-Types)

## Next Steps

To further extend RISC-V support:

1. **RV64A** - Atomic operations (low priority for single-threaded zkVM)
2. **RV64F/D** - Floating-point (not recommended for zkVM)
3. **RV64C** - Compressed instructions (code density optimization)

## Summary

✅ **zigz has complete, production-ready RV64M support** with:
- All 13 RV64M instructions implemented
- Proper handling of edge cases (division by zero, overflow)
- Comprehensive test coverage (16 tests)
- Full zkVM integration
- RISC-V specification compliance

RV64M implementation is complete and ready for use in any RISC-V program targeting zigz!
