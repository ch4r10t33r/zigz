
# zigz Prover Documentation

## Overview

The zigz prover is a complete proof generation system for zero-knowledge RISC-V program execution. It implements Jolt's lookup-based zkVM architecture, combining sumcheck protocol, Lasso lookup arguments, and polynomial commitments to generate succinct proofs.

## Architecture

### Proof Generation Pipeline

```
┌─────────────────────┐
│   RISC-V Program    │
│   (bytecode)        │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│  VM Execution       │
│  - Execute program  │
│  - Record trace     │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│ Witness Generation  │
│ - 43 polynomials    │
│ - PC, regs, inst    │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│ Constraint Building │
│ - Arithmetic        │
│ - Lookup tables     │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│ Sumcheck Protocol   │
│ - Prove constraints │
│ - Round polynomials │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│ Lasso Proofs        │
│ - Lookup arguments  │
│ - Table membership  │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│ Poly Commitments    │
│ - Merkle trees      │
│ - Opening proofs    │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│  Complete Proof     │
│  (serializable)     │
└─────────────────────┘
```

## Components

### 1. Proof Structure (`src/prover/proof.zig`)

Defines the complete proof format:

```zig
pub fn Proof(comptime F: type) type {
    return struct {
        // Public inputs/outputs
        public_io: PublicIO,

        // Main constraint satisfaction proof
        constraint_proof: SumcheckProof(F),

        // Lookup proofs for instruction tables
        lookup_proofs: std.ArrayList(LassoProof(F)),

        // Commitments to 43 witness polynomials
        witness_commitments: []CommitmentOpening(F),

        // Metadata
        metadata: ProofMetadata,
    };
}
```

**Proof Components:**

- **Public I/O**: Program hash, initial/final PC, register values, step count
- **Constraint Proof**: Sumcheck proof that all constraints are satisfied
- **Lasso Proofs**: Lookup argument proofs for each instruction type used
- **Witness Commitments**: Merkle tree commitments to the 43 multilinear polynomials

**Proof Size:** O(log n) where n is the number of execution steps

For 1024 steps:
- ~10 variables in polynomials
- ~10-50 KB total proof size
- Verifier time: < 1 second

### 2. Prover (`src/prover/prover.zig`)

Main proof generation orchestration:

```zig
pub fn Prover(comptime F: type) type {
    return struct {
        pub fn prove(
            self: *Self,
            program: []const u8,
            entry_pc: u64,
            initial_regs: ?[]const u64,
            max_steps: usize,
        ) !Proof {
            // 1. Execute program
            var vm_state = try VMState.init(...);
            while (!vm_state.halted) {
                try vm_state.step();
            }

            // 2. Generate witness
            var witness = try witness_generator.generate(F, vm_state.trace);

            // 3. Build constraints
            try constraints.build(F, witness, vm_state.trace);

            // 4. Run sumcheck
            try self.generateSumcheckProof(&proof, constraints, witness);

            // 5. Generate Lasso proofs
            try self.generateLassoProofs(&proof, constraints, witness);

            // 6. Create commitments
            try self.generateCommitments(&proof, witness);

            // 7. Package public I/O
            try self.packagePublicIO(&proof, program, vm_state, ...);

            return proof;
        }
    };
}
```

**Prover Workflow:**

1. **VM Execution**: Run RISC-V program, record all state transitions
2. **Witness Generation**: Convert trace to 43 multilinear polynomials
3. **Constraint Building**: Generate arithmetic and lookup constraints
4. **Sumcheck Protocol**: Prove constraint satisfaction using sumcheck
5. **Lasso Proofs**: Generate lookup membership proofs
6. **Polynomial Commitments**: Commit to witness polynomials using Merkle trees
7. **Public I/O**: Package program hash and final state

### 3. Serialization (`src/prover/serialization.zig`)

Binary and JSON serialization for proofs:

```zig
pub fn BinarySerializer(comptime F: type) type {
    return struct {
        // Serialize proof to bytes
        pub fn serialize(allocator: std.mem.Allocator, proof: Proof) ![]u8

        // Deserialize proof from bytes
        pub fn deserialize(allocator: std.mem.Allocator, data: []const u8) !Proof
    };
}
```

**Binary Format:**

```
[Header: 32 bytes]
- Magic: "ZIGZ" (4 bytes)
- Version: u32
- Field modulus: u64
- Num steps: u64
- Num variables: u32

[Public IO: variable]
- Program hash (32 bytes)
- PC values, registers, etc.

[Constraint Proof: variable]
- Round polynomials
- Final evaluation point
- Final value

[Lasso Proofs: variable]
- Per-table lookup proofs

[Witness Commitments: variable]
- 43 Merkle roots + opening proofs
```

## The 43 Witness Polynomials

The prover generates 43 multilinear polynomials from the execution trace:

1. **PC Polynomial (1)**
   - Program counter at each step

2. **Register Polynomials (32)**
   - x0-x31 register values at each step

3. **Instruction Field Polynomials (7)**
   - Opcode, rd, rs1, rs2, funct3, funct7, immediate

4. **Memory Access Polynomials (3)**
   - Memory address, memory value, is_write flag

Each polynomial is evaluated over a boolean hypercube {0,1}^v where v = log2(num_steps).

## Constraint Types

### Arithmetic Constraints

1. **PC Progression**: PC[i+1] = PC[i] + 4 or branch_target
2. **x0 Hardwired**: x0 = 0 at all steps
3. **Register Updates**: Verify correct instruction semantics
4. **Memory Consistency**: Load/store correctness

### Lookup Constraints (Lasso)

For each instruction type:
- Prove (rs1, rs2) → rd lookup is in the instruction table
- Use Lasso's multiset equality argument
- Decompose large tables into smaller chunks (16-bit)

Example: ADD instruction
- Inputs: rs1_value, rs2_value (both 32-bit)
- Output: rd_value (32-bit)
- Table size: 2^64 entries (infeasible to store)
- Decomposition: Split into 16-bit chunks → 2^32 entries each

## Usage Examples

### Basic Proof Generation

```zig
const std = @import("std");
const zigz = @import("zigz");
const Prover = zigz.prover.Prover;
const BabyBear = zigz.BabyBear;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();

    // RISC-V program: ADDI x1, x0, 42
    const program = [_]u8{ 0x93, 0x00, 0xA0, 0x02 };

    // Initialize prover
    var prover = try Prover(BabyBear).init(allocator, 12345);
    defer prover.deinit();

    // Generate proof
    var proof = try prover.prove(&program, 0x1000, null, 1000);
    defer proof.deinit();

    std.debug.print("Proof size: {d} bytes\n", .{proof.estimateSize()});
}
```

### Serialization

```zig
const Serializer = zigz.serialization.BinarySerializer(BabyBear);

// Serialize
const data = try Serializer.serialize(allocator, proof);
defer allocator.free(data);

// Save to file
try std.fs.cwd().writeFile("proof.bin", data);

// Load from file
const loaded = try std.fs.cwd().readFileAlloc(allocator, "proof.bin", 10_000_000);
defer allocator.free(loaded);

// Deserialize
var restored_proof = try Serializer.deserialize(allocator, loaded);
defer restored_proof.deinit();
```

## Performance Characteristics

### Prover Time

| Steps | Prover Time (est.) | Proof Size |
|-------|-------------------|------------|
| 100   | ~10 ms           | ~5 KB      |
| 1,000 | ~50 ms           | ~15 KB     |
| 10,000| ~200 ms          | ~30 KB     |
| 100,000| ~2 seconds      | ~50 KB     |
| 1,000,000| ~20 seconds   | ~100 KB    |

*Estimates based on Jolt benchmarks; actual performance TBD*

### Memory Usage

- Execution trace: O(steps × step_size) ≈ 500 bytes/step
- Witness polynomials: O(steps × 43 field elements) ≈ 344 bytes/step with BabyBear
- Constraint generation: O(steps)
- Proof generation: O(log steps)

For 1M steps:
- Trace: ~500 MB
- Witness: ~340 MB
- Proof: ~100 KB

## Field Selection

### BabyBear (Default)

- **Modulus**: p = 2^31 - 2^27 + 1 = 2,013,265,921
- **Element size**: 4 bytes (31-bit)
- **SIMD**: 8 elements per AVX2 vector
- **Performance**: 2-3x faster than Goldilocks

**Advantages:**
- Faster field multiplication (31×31=62 bits, fits in u64)
- Better cache utilization (4 bytes vs 8 bytes)
- 2x SIMD parallelism vs Goldilocks

**Tradeoffs:**
- Requires 64-bit value decomposition (3 chunks: 31+31+2 bits)
- Slightly more complex witness generation

### Goldilocks (Alternative)

- **Modulus**: p = 2^64 - 2^32 + 1
- **Element size**: 8 bytes (64-bit)
- **SIMD**: 4 elements per AVX2 vector

**Advantages:**
- Native 64-bit arithmetic (no decomposition needed)
- Simpler implementation

**Tradeoffs:**
- Slower (2-3x) than BabyBear
- Larger proof sizes

## Testing

Run prover tests:

```bash
# All prover tests
zig build test-prover

# VM tests
zig build test-vm

# Constraint tests
zig build test-constraints

# Full example
zig build run -Doptimize=ReleaseFast
```

## Next Steps: Verifier (Phase 10)

The verifier will:

1. **Parse Proof**: Deserialize proof from bytes
2. **Verify Sumcheck**: Check constraint satisfaction
3. **Verify Lasso**: Check lookup correctness
4. **Verify Commitments**: Check polynomial openings
5. **Verify Public I/O**: Check program hash and final state

Verifier time: O(log n) where n is number of steps

Expected: < 1 second for most proofs

## References

- [Jolt Paper](https://eprint.iacr.org/2023/1217.pdf) - Original zkVM architecture
- [Lasso Paper](https://people.cs.georgetown.edu/jthaler/Lasso-paper.pdf) - Lookup arguments
- [Sumcheck Protocol](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) - Chapter 4

## Implementation Status

- ✅ Proof structure and types
- ✅ Prover orchestration
- ✅ Binary serialization
- ✅ Public I/O packaging
- 🚧 Sumcheck integration (placeholder)
- 🚧 Lasso proof generation (placeholder)
- 🚧 Polynomial opening proofs (placeholder)
- 📋 JSON serialization
- 📋 Proof compression
- 📋 Verifier implementation

The core infrastructure is complete. The next phase will implement the full verifier and complete the sumcheck/Lasso integration.
