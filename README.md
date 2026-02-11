# zigz

**A zero-knowledge virtual machine written in Zig, inspired by Jolt's lookup-based proving architecture.**

---

## Overview

zigz is a zkVM (zero-knowledge virtual machine) that allows you to generate succinct cryptographic proofs of RISC-V program execution. It's designed with simplicity and clarity as first principles, following Jolt's innovative architecture.

### Why zigz?

- **Simplicity**: Inspired by Jolt's < 25k lines codebase, emphasizing readable, maintainable code
- **Modern Architecture**: Uses sumcheck protocol + Lasso lookup argument instead of traditional STARK/SNARK approaches
- **Zig-powered**: Leverages Zig's compile-time capabilities, memory safety, and performance
- **Educational**: Clear separation of concerns makes it ideal for learning zkVM internals

### Key Features (Planned)

- ✅ Generic finite field arithmetic with compile-time specialization
- ✅ Multilinear polynomial operations
- ✅ Sumcheck protocol implementation
- ✅ Lasso lookup argument (Jolt's innovation)
- ✅ RISC-V RV32I instruction set support
- ✅ Full prover and verifier

---

## Architecture

zigz uses a **lookup-based proving system** inspired by [Jolt](https://eprint.iacr.org/2023/1217.pdf):

1. **Sumcheck Protocol**: Core proof primitive for verifying polynomial identities
2. **Lasso Lookup Argument**: Efficient lookup tables for instruction semantics
3. **RISC-V Target**: Proves execution of standard RISC-V programs
4. **Modular Design**: Clean separation between VM, constraints, and proof system

### How it Works

```
RISC-V Program
     ↓
VM Execution → Execution Trace
     ↓
Constraint Generation → Witness Polynomials
     ↓
Sumcheck + Lasso → Cryptographic Proof
     ↓
Verifier → Accept/Reject
```

See [MODULES.md](MODULES.md) for detailed architecture documentation.

---

## Getting Started

### Prerequisites

- Zig 0.14.0 or later
- Git (for dependency management)

### Installation

```bash
# Clone the repository
git clone https://github.com/ch4r10t33r/zigz.git
cd zigz

# Build the project
zig build

# Run tests
zig build test
```

### Quick Example

```bash
# Run zigz (currently prints banner)
zig build run
```

---

## Project Status

**Current Phase**: Phase 4 - RISC-V Instruction Set ✅

zigz is in early development. Core components (field arithmetic, polynomials, sumcheck, RV32I ISA) are complete. Lasso lookup argument is next.

### Implementation Roadmap

| Phase | Status | Description |
|-------|--------|-------------|
| 0 | ✅ Complete | Project structure & build system |
| 1 | ✅ Complete | Field arithmetic & basic crypto |
| 2 | ✅ Complete | Polynomial operations |
| 3 | ✅ Complete | Sumcheck protocol |
| 4 | ✅ Complete | RISC-V instruction set |
| 5 | 📋 Planned | Lasso lookup argument |
| 6 | 📋 Planned | VM state machine |
| 7 | 📋 Planned | Constraint generation |
| 8 | 📋 Planned | Full prover |
| 9 | 📋 Planned | Full verifier |
| 10 | 📋 Planned | Integration & optimization |

See the [implementation plan](/sessions/sharp-eager-einstein/mnt/.claude/plans/swift-toasting-conway.md) for detailed timeline.

---

## Development

### Building

```bash
# Build in debug mode
zig build

# Build optimized binary
zig build -Doptimize=ReleaseFast

# Run the executable
zig build run
```

### Testing

```bash
# Run all tests
zig build test

# Run specific module tests (as modules are implemented)
zig build test-field      # Field arithmetic tests
zig build test-poly       # Polynomial tests
# More test targets will be added
```

### Project Structure

```
zigz/
├── src/
│   ├── core/          # Cryptographic primitives
│   ├── poly/          # Polynomial operations
│   ├── proofs/        # Sumcheck protocol
│   ├── lookups/       # Lasso implementation
│   ├── isa/           # RISC-V instruction set
│   ├── constraints/   # Constraint generation
│   ├── vm/            # Virtual machine
│   ├── prover/        # Proof generation
│   ├── verifier/      # Proof verification
│   └── main.zig       # Entry point
├── tests/             # Integration tests
├── build.zig          # Build configuration
├── build.zig.zon      # Package manifest
├── MODULES.md         # Architecture documentation
└── README.md          # This file
```

See [MODULES.md](MODULES.md) for detailed module documentation.

---

## Contributing

zigz is in active early development. Contributions are welcome once the core architecture stabilizes (after Phase 3).

### Development Principles

1. **Simplicity First**: Clear, readable code over clever optimizations
2. **Test Everything**: Every component has comprehensive tests
3. **Document Intent**: Explain the "why" not just the "what"
4. **Modular Design**: Clean interfaces between components
5. **Zig Idioms**: Leverage Zig's strengths (comptime, error handling, etc.)

---

## Technical Background

### What is a zkVM?

A zero-knowledge virtual machine allows you to:
1. Execute a program (like RISC-V assembly)
2. Generate a cryptographic proof of correct execution
3. Verify the proof quickly without re-executing the program
4. The proof reveals nothing about private inputs (zero-knowledge)

### Why Jolt's Architecture?

Traditional zkVMs use STARK or SNARK constraint systems (AIR, R1CS, Plonk). Jolt pioneered a **lookup-based** approach:

- **Simpler**: Instructions defined by lookup tables (< 50 lines each)
- **Faster**: Lookup arguments (Lasso) are more efficient than constraints
- **Modular**: Clean separation between VM and proof system
- **Extensible**: Easy to add new instructions or opcodes

### Key Papers

- [Jolt: SNARKs for Virtual Machines via Lookups](https://eprint.iacr.org/2023/1217.pdf)
- [Lasso and Jolt: Lookup Arguments and zkVMs](https://a16zcrypto.com/posts/article/building-jolt/)
- [Unlocking the Lookup Singularity with Lasso](https://people.cs.georgetown.edu/jthaler/Lasso-paper.pdf)

---

## Performance Goals

Target performance (after Phase 10):

- **Prover Time**: ~1-2 seconds per 1M RISC-V cycles
- **Proof Size**: ~100-500 KB per proof
- **Verifier Time**: < 1 second for typical proofs
- **Memory**: Efficient table decomposition for large instruction lookups

These are aspirational targets based on Jolt's benchmarks. Actual performance will be measured and optimized in Phase 10.

---

## Dependencies

- **[hash-zig](https://github.com/blockblaz/hash-zig)**: Cryptographic hashing (Poseidon2, etc.)
- **Zig Standard Library**: Core functionality

External dependencies are kept minimal to reduce complexity and improve auditability.

---

## License

[Add license information]

---

## Acknowledgments

- **Jolt Team** ([a16z crypto](https://a16zcrypto.com/)): For the innovative zkVM architecture
- **Justin Thaler**: For the Lasso lookup argument and sumcheck research
- **RISC-V Foundation**: For the open ISA specification
- **Zig Community**: For the excellent programming language and ecosystem

---

## Contact

- **Repository**: [https://github.com/ch4r10t33r/zigz](https://github.com/ch4r10t33r/zigz)
- **Issues**: [GitHub Issues](https://github.com/ch4r10t33r/zigz/issues)

---

**Status**: 🚧 Early Development (Phase 0 Complete) 🚧