# zigz zkVM Blog Series

Educational deep dives into the components and architecture of zigz, a zero-knowledge virtual machine written in Zig.

## Series Overview

This blog series breaks down zigz's implementation, explaining the cryptographic primitives, proof systems, and architectural decisions behind the zkVM. Each post builds on previous concepts, starting from the mathematical foundations and progressing to the complete proof system.

---

## Published Posts

### Part 1: [Field Arithmetic: The Foundation of Zero-Knowledge Virtual Machines](01-field-arithmetic-in-zkvm.md)

**Topics covered:**
- What are finite fields and why zkVMs use them
- Prime field arithmetic (addition, multiplication, inversion)
- Field selection criteria for zkVMs
- BabyBear, Goldilocks, and Mersenne fields
- zigz's compile-time generic field implementation
- Performance implications of field choice

**Key takeaway:** Every zkVM operation—from simple addition to complex polynomial commitments—ultimately relies on efficient, exact finite field arithmetic.

---

### Part 2: [Polynomials in zkVMs: From Univariate to Multilinear](02-polynomials-in-zkvm.md)

**Topics covered:**
- Univariate polynomials: definition, operations, and uses
- Multilinear polynomials: boolean hypercube representation
- Partial evaluation and the sumcheck protocol
- Lasso lookup argument and table decomposition
- When to use univariate vs. multilinear
- zigz's dual polynomial implementation

**Key takeaway:** Polynomials are the language of zero-knowledge proofs. Understanding univariate and multilinear polynomials is essential for building efficient zkVMs.

---

## Upcoming Posts

### Part 3: The Sumcheck Protocol (Coming Soon)
- Interactive proof protocol for polynomial sums
- Round-by-round execution flow
- Prover and verifier implementation
- Fiat-Shamir transformation for non-interactivity
- Role in Jolt's architecture

### Part 4: Lasso Lookup Arguments (Coming Soon)
- Why lookup tables for instruction semantics
- Multilinear decomposition for large tables
- Memory checking and lookup proofs
- Offline memory checking technique
- Implementation in zigz

### Part 5: RISC-V Execution Model (Coming Soon)
- RV64I and RV64M instruction sets
- VM state machine and execution traces
- Sparse memory representation
- Constraint generation from execution
- Why RISC-V for zkVMs

### Part 6: Polynomial Commitments (Coming Soon)
- Hash-based Merkle tree commitments
- Opening proofs and verification
- Transparency vs. trusted setup
- Post-quantum security
- Batching and optimization

### Part 7: Full Prover Pipeline (Coming Soon)
- From execution trace to proof
- Constraint system construction
- Witness polynomial generation
- Proof serialization
- Performance benchmarks

### Part 8: Verification and Security (Coming Soon)
- O(log n) verification time
- Fiat-Shamir vulnerability fixes (Jolt PR #981)
- Opening claims binding
- Transcript management
- Security model and assumptions

---

## Target Audience

These posts are written for:
- **Cryptography engineers** building or understanding zkVMs
- **Systems programmers** interested in zero-knowledge proofs
- **Researchers** exploring modern proof systems (Jolt, Lasso, sumcheck)
- **Zig developers** curious about compile-time metaprogramming for crypto

**Prerequisites:**
- Basic understanding of modular arithmetic
- Familiarity with polynomials (high school algebra)
- Some programming experience (preferably systems languages)
- No prior cryptography knowledge required!

---

## Why This Series?

Most zkVM documentation falls into two camps:
1. **Academic papers** - rigorous but inaccessible
2. **Implementation docs** - code-focused without theory

This series bridges the gap:
- ✅ **Rigorous explanations** with clear examples
- ✅ **Real code** from zigz's implementation
- ✅ **Practical insights** on performance and trade-offs
- ✅ **Progressive complexity** from basics to advanced

---

## Contributing

Found an error? Have a suggestion? Want to contribute a post?

1. Open an issue on the [zigz repository](https://github.com/ch4r10t33r/zigz/issues)
2. Submit a pull request with corrections
3. Propose new topics you'd like to see covered

All blog posts are written in Markdown and committed to the `blog/` directory.

---

## License

Blog posts are licensed under CC BY 4.0 (Creative Commons Attribution 4.0 International).

You are free to:
- Share and redistribute
- Adapt and build upon

With attribution to the zigz project.

---

## Stay Updated

- **Repository:** [github.com/ch4r10t33r/zigz](https://github.com/ch4r10t33r/zigz)
- **Issues:** [github.com/ch4r10t33r/zigz/issues](https://github.com/ch4r10t33r/zigz/issues)
- Watch the repository for updates when new posts are published!

---

*zigz is an open-source zkVM written in Zig, inspired by Jolt's lookup-based architecture.*
