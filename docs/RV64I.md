# RV64I Support in zigz

## Overview

zigz has **complete RV64I (64-bit RISC-V)** support, including all 64-bit instructions and proper sign-extension semantics. The VM can execute both RV32I and RV64I programs.

## RV64I Features

### 1. 64-bit Registers

- All 32 general-purpose registers are 64 bits wide (XLEN=64)
- Program counter (PC) is 64 bits
- Full 64-bit address space supported

### 2. RV64I-Specific Instructions

#### Doubleword Load/Store
- **LD** - Load Doubleword (64-bit load)
- **SD** - Store Doubleword (64-bit store)

#### Word Operations (*W suffix)
These operate on the lower 32 bits and sign-extend the result to 64 bits:

**Immediate Operations:**
- **ADDIW** - Add Immediate Word
- **SLLIW** - Shift Left Logical Immediate Word
- **SRLIW** - Shift Right Logical Immediate Word
- **SRAIW** - Shift Right Arithmetic Immediate Word

**Register-Register Operations:**
- **ADDW** - Add Word
- **SUBW** - Subtract Word
- **SLLW** - Shift Left Logical Word
- **SRLW** - Shift Right Logical Word
- **SRAW** - Shift Right Arithmetic Word

#### Load Word Unsigned
- **LWU** - Load Word Unsigned (zero-extends 32-bit value to 64 bits)

### 3. Sign Extension Semantics

**Key Difference from RV32I:**

In RV32I, `LW` loads a 32-bit word into a 32-bit register.

In RV64I:
- `LW` loads a 32-bit word and **sign-extends** it to 64 bits
- `LWU` loads a 32-bit word and **zero-extends** it to 64 bits

Example:
```
Memory[0] = 0xFFFFFFFF (all bits set)

LW x10, 0(x0)   → x10 = 0xFFFFFFFFFFFFFFFF (sign-extended)
LWU x11, 0(x0)  → x11 = 0x00000000FFFFFFFF (zero-extended)
```

### 4. Word Operations Behavior

Word operations (*W instructions) have special semantics:

1. **Truncate operands** to 32 bits (ignore high 32 bits)
2. **Perform operation** on 32-bit values
3. **Sign-extend result** to 64 bits

Example:
```zig
// x10 = 0x7FFFFFFF (max positive 32-bit int)
ADDIW x11, x10, 1

// Operation:
// 1. Truncate x10 to 32 bits: 0x7FFFFFFF
// 2. Add 1: 0x7FFFFFFF + 1 = 0x80000000
// 3. Sign-extend to 64 bits: 0xFFFFFFFF80000000

// Result: x11 = 0xFFFFFFFF80000000 (negative in 64-bit)
```

## Implementation

### Instruction Decoder

`src/isa/rv64i.zig` implements the RV64I instruction decoder with:
- All RV64I opcodes (OP_32, OP_IMM_32)
- 64-bit immediate sign extension
- Helper methods: `isRV64IOnly()`, `isWordOperation()`

### VM State Machine

`src/vm/state.zig` implements RV64I execution with:
- `executeOP32()` - Word register-register operations
- `executeOPIMM32()` - Word immediate operations
- `executeLOAD()` - Handles LD and LWU
- `executeSTORE()` - Handles SD

All word operations properly truncate, operate, and sign-extend.

## Testing

### Unit Tests

**Instruction Decoder** (`src/isa/rv64i.zig`):
- ✅ ADDI (RV32I compatibility)
- ✅ ADDIW (word immediate)
- ✅ LD (load doubleword)
- ✅ SD (store doubleword)
- ✅ LWU (load word unsigned)
- ✅ ADDW (add word)
- ✅ 64-bit sign extension
- ✅ Format detection

**VM Execution** (`tests/test_rv64i.zig`):
- ✅ LD/SD roundtrip
- ✅ LW vs LWU (sign vs zero extension)
- ✅ ADDIW overflow and sign extension
- ✅ ADDW overflow and sign extension
- ✅ SUBW underflow
- ✅ SLLW shift left
- ✅ SRLW logical right shift
- ✅ SRAW arithmetic right shift
- ✅ 64-bit address space
- ✅ Word operations ignore high bits
- ✅ Negative result sign extension

### Running Tests

```bash
# RV64I instruction decoder tests
zig build test-rv64i

# RV64I VM execution tests
zig build test-rv64i-vm

# All tests
zig build test-all
```

## Usage Examples

### Example 1: Using Full 64-bit Values

```zig
// Store and load 64-bit value
LI x10, 0x123456789ABCDEF0
SD x10, 0(x0)
LD x11, 0(x0)
// x11 now contains 0x123456789ABCDEF0
```

### Example 2: Word Operations

```zig
// Demonstrate word operation sign extension
LI x10, 0x7FFFFFFF      // Max positive 32-bit int
ADDIW x11, x10, 1       // Add 1 (word operation)
// x11 = 0xFFFFFFFF80000000 (sign-extended negative)

// Regular 64-bit add would give different result:
LI x10, 0x7FFFFFFF
ADDI x11, x10, 1        // Regular 64-bit add
// x11 = 0x0000000080000000 (positive 64-bit value)
```

### Example 3: LW vs LWU

```zig
// Store negative 32-bit value
LI x10, 0xFFFFFFFF
SW x10, 0(x0)

// Load with sign extension
LW x11, 0(x0)
// x11 = 0xFFFFFFFFFFFFFFFF (sign-extended to all 1s)

// Load with zero extension
LWU x12, 0(x0)
// x12 = 0x00000000FFFFFFFF (zero-extended)
```

## Differences from RV32I

| Feature | RV32I | RV64I |
|---------|-------|-------|
| XLEN (register width) | 32 bits | 64 bits |
| Address space | 32-bit (4 GB) | 64-bit (16 EB) |
| LD/SD | ❌ Not present | ✅ 64-bit load/store |
| LWU | ❌ Not present | ✅ Zero-extend word load |
| LW behavior | Load 32-bit word | Load and sign-extend to 64 bits |
| *W instructions | ❌ Not present | ✅ Word ops with sign-extend |
| Immediate size | 32 bits (i32) | 64 bits (i64) |

## Compatibility

- **RV32I programs** can run on RV64I hardware
- All RV32I instructions are valid RV64I instructions
- The main difference is register width and memory addressing

## Performance

RV64I in zigz has the same performance characteristics as RV32I:
- O(log n) proof size (same polynomial count)
- O(log n) verification time
- Witness generation is slightly larger (64-bit values vs 32-bit)

The field operations remain the same (BabyBear or Goldilocks), so proving performance is comparable.

## zkVM Integration

The zkVM prover/verifier work identically for RV32I and RV64I:

1. **Witness Generation**: Records 64-bit register values
2. **Polynomial Encoding**: Each register becomes a witness polynomial
3. **Constraints**: Same constraint structure, different value ranges
4. **Proof Size**: O(log n) regardless of register width

## Limitations

Current implementation does not support:
- **RV64M** extension (multiply/divide) - use RV32M
- **RV64F/D** extensions (floating-point)
- **RV64A** extension (atomics)
- **RV64C** extension (compressed instructions)
- **Privileged ISA** (CSR operations are minimal)

These can be added incrementally as needed.

## References

- [RISC-V Instruction Set Manual](https://riscv.org/technical/specifications/)
- [RV64I Base Integer Instruction Set](https://riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf) (Chapter 5)
- [Jolt zkVM](https://github.com/a16z/jolt) (inspiration for this implementation)

## Next Steps

To further extend RV64I support:

1. **RV64M Extension** - Multiply/divide for 64-bit values
2. **Performance Optimization** - Optimize 64-bit field operations
3. **Witness Optimization** - Compress 64-bit witness polynomials
4. **Extended Examples** - More complex RV64I programs

## Summary

✅ **zigz has complete, production-ready RV64I support** with:
- All RV64I instructions implemented
- Proper sign-extension semantics
- Comprehensive test coverage
- Full zkVM integration

The implementation is spec-compliant and ready for use!
