# zigz Module Architecture

This document describes the modular architecture of zigz and the dependencies between modules.

## Module Overview

zigz is organized into logical modules that build upon each other to create a complete zero-knowledge virtual machine. The architecture follows a layered approach, where each layer depends only on layers below it.

## Module Structure

```
zigz/
├── src/
│   ├── core/          # Layer 0: Foundation - Cryptographic primitives
│   ├── poly/          # Layer 1: Polynomial operations
│   ├── proofs/        # Layer 2: Proof system primitives
│   ├── lookups/       # Layer 3: Lookup arguments (Lasso)
│   ├── isa/           # Layer 3: Instruction set definitions
│   ├── constraints/   # Layer 4: Constraint generation
│   ├── vm/            # Layer 4: Virtual machine
│   ├── prover/        # Layer 5: Proof generation
│   ├── verifier/      # Layer 5: Proof verification
│   └── main.zig       # Entry point
└── tests/             # Test suite
```

## Dependency Graph

```
┌─────────────────────────────────────────────────┐
│ Layer 0: Core                                   │
│  - field.zig        (finite field arithmetic)   │
│  - field_presets.zig (common field configs)     │
│  - hash.zig         (hash wrapper)              │
└─────────────────────────────────────────────────┘
                      ↓
┌─────────────────────────────────────────────────┐
│ Layer 1: Polynomials                            │
│  - univariate.zig   (univariate polynomials)    │
│  - multilinear.zig  (multilinear polynomials)   │
│  - lagrange.zig     (Lagrange basis)            │
└─────────────────────────────────────────────────┘
                      ↓
┌─────────────────────────────────────────────────┐
│ Layer 2: Proof Primitives                       │
│  - sumcheck_protocol.zig  (sumcheck state)      │
│  - sumcheck_prover.zig    (prover logic)        │
│  - sumcheck_verifier.zig  (verifier logic)      │
│  - poly_commitment.zig    (commitments)         │
└─────────────────────────────────────────────────┘
                      ↓
         ┌────────────┴────────────┐
         ↓                         ↓
┌──────────────────┐      ┌─────────────────────┐
│ Layer 3: Lookups │      │ Layer 3: ISA        │
│  - table_builder │      │  - rv32i.zig        │
│  - lasso_prover  │      │  - instruction_table│
│  - lasso_verifier│      └─────────────────────┘
└──────────────────┘               ↓
         ↓                         ↓
         └────────────┬────────────┘
                      ↓
┌─────────────────────────────────────────────────┐
│ Layer 4: Constraints & VM                       │
│  - constraints/encoder.zig                      │
│  - constraints/builder.zig                      │
│  - vm/state.zig                                 │
│  - vm/memory.zig                                │
│  - vm/trace.zig                                 │
│  - vm/execute.zig                               │
└─────────────────────────────────────────────────┘
                      ↓
┌─────────────────────────────────────────────────┐
│ Layer 5: Prover & Verifier                      │
│  - prover/prover.zig                            │
│  - prover/proof_serialization.zig               │
│  - verifier/verifier.zig                        │
│  - verifier/benchmarks.zig                      │
└─────────────────────────────────────────────────┘
```

## Module Dependencies (Detailed)

### Layer 0: Core
**No dependencies** (foundational layer)

**Purpose**: Provides cryptographic and mathematical primitives used by all other modules.

**Modules**:
- `field.zig`: Generic finite field arithmetic with compile-time field selection
- `field_presets.zig`: Pre-configured field parameters (Goldilocks, BN254, etc.)
- `hash.zig`: Wrapper around hash-zig for commitment and Fiat-Shamir

**External dependencies**: `hash-zig` (for cryptographic hashing)

### Layer 1: Polynomials
**Dependencies**: `core/*`

**Purpose**: Polynomial evaluation and arithmetic over finite fields.

**Modules**:
- `univariate.zig`: Dense univariate polynomials with Horner evaluation
- `multilinear.zig`: Multilinear polynomials over boolean hypercube
- `lagrange.zig`: Lagrange basis and interpolation

**Key types**:
- `Univariate(FieldType)`: Univariate polynomial generic over field
- `MultilinearPoly(FieldType)`: Multilinear polynomial with partial evaluation

### Layer 2: Proof Primitives
**Dependencies**: `core/*`, `poly/*`

**Purpose**: Core sumcheck protocol and polynomial commitments.

**Modules**:
- `sumcheck_protocol.zig`: Protocol state machine and round management
- `sumcheck_prover.zig`: Prover-side sumcheck implementation
- `sumcheck_verifier.zig`: Verifier-side sumcheck implementation
- `poly_commitment.zig`: Polynomial commitment scheme (initially Merkle-based)

**Key protocols**:
- Interactive sumcheck (Fiat-Shamir for non-interactive)
- Polynomial opening proofs
- Challenge generation

### Layer 3: Lookups & ISA
**Dependencies**: `core/*`, `poly/*`, `proofs/*`

**Purpose**: Instruction set definitions and lookup argument (Lasso).

**Lookups modules**:
- `table_builder.zig`: Construct lookup tables for instructions
- `table_decomposition.zig`: Decompose large tables into subtables
- `lasso_prover.zig`: Lasso lookup argument prover
- `lasso_verifier.zig`: Lasso lookup argument verifier

**ISA modules**:
- `rv32i.zig`: RISC-V RV32I instruction set encoding/decoding
- `instruction_table.zig`: Lookup table metadata for instructions

**Key features**:
- Table-based instruction semantics
- Digit-wise decomposition for memory efficiency
- Sumcheck-based lookup verification

### Layer 4: Constraints & VM
**Dependencies**: `core/*`, `poly/*`, `proofs/*`, `lookups/*`, `isa/*`

**Purpose**: Virtual machine execution and constraint generation.

**Constraints modules**:
- `encoder.zig`: Encode execution traces as field elements
- `builder.zig`: Build constraint polynomials from traces

**VM modules**:
- `state.zig`: VM state (registers, PC, flags)
- `memory.zig`: Memory model with trace recording
- `trace.zig`: Execution trace data structure
- `execute.zig`: Instruction execution engine

**Key workflows**:
1. Execute RISC-V program → generate trace
2. Encode trace → witness polynomials
3. Generate constraints → polynomial equations

### Layer 5: Prover & Verifier
**Dependencies**: All layers below

**Purpose**: End-to-end proof generation and verification.

**Prover modules**:
- `prover.zig`: Orchestrate proof generation
- `proof_serialization.zig`: Serialize/deserialize proofs

**Verifier modules**:
- `verifier.zig`: Proof verification logic
- `benchmarks.zig`: Performance measurement

**Key workflows**:
- **Prover**: program → trace → constraints → sumcheck + Lasso → proof
- **Verifier**: proof → sumcheck verification → Lasso verification → accept/reject

## Testing Strategy

### Unit Tests
Each module has its own test file that can be run independently:

```bash
# Test specific modules
zig build test-field      # Field arithmetic tests
zig build test-poly       # Polynomial tests
# More test targets added as modules are implemented
```

### Integration Tests
Located in `tests/` directory, test cross-module interactions:

```bash
# Run all tests (including integration)
zig build test
```

### Test Organization
- Unit tests: Colocated with source files using Zig's `test` blocks
- Integration tests: Separate files in `tests/` directory
- Property tests: Verify mathematical properties (commutativity, associativity, etc.)
- End-to-end tests: Full programs → proofs → verification

## Build System

The `build.zig` file is organized to support:
1. **Modular compilation**: Each module can be built independently
2. **Selective testing**: Run tests for specific modules
3. **Optimization levels**: Debug, ReleaseSafe, ReleaseFast, ReleaseSmall
4. **Target platforms**: Native and cross-compilation support

### Build Commands

```bash
# Build main executable
zig build

# Run zigz (for demos/experiments)
zig build run

# Run all tests
zig build test

# Run specific module tests
zig build test-field
zig build test-poly
# ... more as modules are added
```

## Implementation Phases

See the main README.md for the complete implementation timeline. Each phase corresponds to implementing one or more layers of this architecture:

- **Phase 0**: Project structure (this document)
- **Phase 1**: Layer 0 (Core)
- **Phase 2**: Layer 1 (Polynomials)
- **Phase 3**: Layer 2 (Proof primitives)
- **Phase 4**: Layer 3 (ISA)
- **Phase 5**: Layer 3 (Lookups)
- **Phase 6-7**: Layer 4 (VM & Constraints)
- **Phase 8-9**: Layer 5 (Prover & Verifier)
- **Phase 10**: Integration & Optimization

## Module Conventions

### File Naming
- Use lowercase with underscores: `multilinear.zig`, `sumcheck_protocol.zig`
- Group related files in same directory

### Code Organization
- Public API at top of file
- Internal helpers below
- Tests at bottom using `test` blocks

### Error Handling
- Use explicit error sets: `error{OutOfMemory, InvalidInput}`
- Return error unions: `!T` for fallible operations
- Propagate errors with `try`

### Generic Types
- Use comptime parameters for type-generic code
- Example: `pub fn Field(comptime modulus: u256) type { ... }`
- Document type constraints and requirements

### Memory Management
- Prefer stack allocation where possible
- Use arena allocators for phase-local allocations
- Always use `defer` for cleanup
- Document ownership and lifetime

## Future Extensions

As the project evolves, additional modules may be added:

- `src/recursion/`: Proof recursion and aggregation
- `src/optimization/`: Performance-specific implementations
- `src/extensions/`: Additional RISC-V extensions (M, A, F, D, V)
- `benchmarks/`: Comprehensive benchmarking suite

## References

- [Jolt Paper](https://eprint.iacr.org/2023/1217.pdf) - The Jolt zkVM architecture
- [Lasso Paper](https://people.cs.georgetown.edu/jthaler/Lasso-paper.pdf) - The Lasso lookup argument
- [RISC-V ISA Manual](https://riscv.org/technical/specifications/) - RISC-V specifications
- [Zig Documentation](https://ziglang.org/documentation/master/) - Zig language reference
