# zigz Examples

This directory contains examples for zigz — from the core sumcheck protocol up to the full
zkVM prove-verify workflow.

## Quick Start

```bash
# Run the end-to-end Fibonacci demo (guest + host, like SP1's fibonacci example)
zig build fibonacci

# Run all other examples
zig build sumcheck_basic && ./zig-out/bin/sumcheck_basic
zig build prover_verifier_demo && ./zig-out/bin/prover_verifier_demo
```

## Fibonacci: End-to-End zkVM Demo

The Fibonacci example mirrors [SP1's fibonacci example](https://github.com/succinctlabs/sp1/tree/main/examples/fibonacci).
Both follow the same pattern: a guest program compiles to a RISC-V ELF; a host loads the ELF,
proves its execution, and verifies the proof.

### Architecture comparison

| | SP1 | zigz |
|---|---|---|
| Guest language | Rust | Zig |
| Guest target | `riscv32im-succinct-zkvm-elf` | `riscv64-freestanding` |
| Read from host | `sp1_zkvm::io::read::<T>()` | `io.read(T)` (from `zigz_io`) |
| Write to host | `sp1_zkvm::io::commit(&val)` | `io.commit(val)` (from `zigz_io`) |
| Host proves | `sp1_sdk::ProverClient::prove(ELF, stdin)` | `zigz.Prover.prove(elf_bytes, ..., input)` |
| Host verifies | `sp1_sdk::ProverClient::verify(proof, vk)` | `zigz.Verifier.verify(proof, elf_bytes)` |
| Public outputs | `sp1_sdk::SP1PublicValues` | `proof.public_io.outputs` |

### Files

- **`fibonacci_guest/src/main.zig`** — the guest program that runs *inside* the VM
- **`fibonacci.zig`** — the host that provides input, proves, and verifies
- **`../src/io.zig`** — the `zigz_io` package imported by the guest

### How it works

1. `zig build fibonacci` cross-compiles `fibonacci_guest` to a RISC-V ELF (in `zig-out/bin/`).
2. The host locates and reads the ELF at runtime, then calls `zigz.elf.load()` to extract
   the entry PC and PT_LOAD segments.
3. The host passes `n` to the prover via an input tape (`input: &[_]u64{n}`).
4. Inside the VM, the guest reads `n` with `io.read(u64)`, computes fib(n) and fib(n+1),
   then calls `io.commit(a)` and `io.commit(b)` to write public outputs.
5. Sumcheck + Lasso + Merkle commitments produce a succinct proof.
6. Committed values appear in `proof.public_io.outputs` — no register inspection needed.
7. The verifier checks the proof in O(log steps) — without re-executing.

### Guest I/O (`zigz_io`)

The `zigz_io` package (`src/io.zig`) is the zigz equivalent of `sp1_zkvm::io`. Import it in any
freestanding guest program:

```zig
const io = @import("zigz_io");

export fn _start() noreturn {
    const n = io.read(u64);   // host input tape  → ECALL a7=2
    io.commit(result);         // public output tape → ECALL a7=1
    asm volatile ("ebreak");
    unreachable;
}
```

The host receives committed values in `proof.public_io.outputs[]` after proving.

---

## Examples Overview

### 1. `sumcheck_basic.zig` - Introduction to Sumcheck

**What it shows:**
- Complete prover-verifier interaction
- 2-variable multilinear polynomial
- Round polynomial generation
- Verification process with detailed output
- Educational commentary explaining each step

**Run this first** to understand how sumcheck works!

**Expected output:**
- Polynomial setup and claimed sum
- Round polynomials for each variable
- Verification result with explanation
- Complexity comparison (O(v) vs O(2^v))

---

### 2. `sumcheck_dishonest.zig` - Catching Cheaters

**What it shows:**
- How sumcheck catches dishonest provers
- Scenario 1: Wrong claimed sum → **Caught!**
- Scenario 2: Tampered round polynomial → **Caught!**
- Scenario 3: Honest prover → Accepted
- Why soundness guarantees are important

**Key lesson:** You can't cheat sumcheck! 🛡️

**Expected output:**
- Three test scenarios
- Detection of each type of fraud
- Explanation of soundness properties

---

### 3. `sumcheck_scalability.zig` - Performance Analysis

**What it shows:**
- How sumcheck scales with polynomial size
- Testing 1 to 8 variables
- Proof size comparison
- Verifier work: O(v) vs naive O(2^v)
- Timing measurements for larger cases

**Key insight:** Exponential savings in verification!

**Expected output:**
- Table showing vars, points, proof size, and naive work
- Analysis of verification complexity
- Real-world zkVM implications

---

### 4. `sumcheck_constraint.zig` - zkVM Application

**What it shows:**
- How sumcheck proves computational constraints
- Example: Proving 4 addition operations are correct
- Constraint polynomial: C(step) = result - (a + b)
- Proving Σ C²(step) = 0 (all constraints satisfied)
- Detecting incorrect computations

**Key lesson:** Foundation of zkVM constraint verification!

**Expected output:**
- Execution trace of 4 additions
- Constraint polynomial construction
- Proof that all constraints hold (sum = 0)
- Example with incorrect computation (sum ≠ 0)
- Explanation of how this applies to real zkVMs

---

## Understanding the Output

### Round Polynomials

Each round, the prover sends a univariate polynomial `g(X)`:

```
Round 1: g₁(X) = 4 + 2·X
  g(0) = 4, g(1) = 6, g(0)+g(1) = 10 ✓
```

The verifier checks: **g(0) + g(1) = claimed_sum**

### Challenges

Using Fiat-Shamir, random challenges are derived from the transcript:

```
Challenge 1: r₁ = 5 (from hash of g₁)
Challenge 2: r₂ = 7 (from hash of g₂)
```

These challenges "zoom in" on a random point `(r₁, r₂)`.

### Final Check

The verifier evaluates the original polynomial at the final point:

```
Final point: (5, 7)
Expected: p(5, 7) = 12
Claimed: 12
✅ Match!
```

---

## Educational Notes

### What is Sumcheck Proving?

Given a multilinear polynomial `p(x₁, ..., xᵥ)`, sumcheck proves:

```
H = Σ p(b₁, ..., bᵥ) over all (b₁, ..., bᵥ) ∈ {0,1}^v
```

**Without** revealing the polynomial itself!

### Why O(v) Verification?

- Naive: Check 2^v evaluations → Exponential
- Sumcheck: Check v round polynomials + 1 oracle → Logarithmic

For v=20 variables:
- Naive: 1,048,576 checks
- Sumcheck: 21 checks
- **Savings: ~50,000x!**

### Connection to zkVMs

In a zkVM:
1. **Execution trace** → Multilinear polynomial
2. **Constraints** → Polynomial identities
3. **Sumcheck** → Prove constraints hold
4. **Result** → Succinct proof of correct execution!

---

## Next Steps

After understanding these examples:

1. **Implement Phase 4**: RISC-V instruction set
2. **Implement Phase 5**: Lasso lookup argument
3. **Combine**: Use sumcheck + Lasso for full zkVM

The sumcheck protocol you've learned here is the **heart** of Jolt's zkVM!

---

## Troubleshooting

### Build Errors

If you get import errors, make sure you're building from the project root:

```bash
cd /path/to/zigz
zig build-exe examples/sumcheck_basic.zig --mod hash-zig::.zig-cache/...
```

### Understanding the Code

Each example is heavily commented. Read through the code alongside the output to understand:
- How prover generates round polynomials
- How verifier checks each round
- How challenges are generated
- How the final oracle call works

---

## Further Reading

- [Sumcheck Protocol (Wikipedia)](https://en.wikipedia.org/wiki/Sumcheck_protocol)
- [Jolt Paper](https://eprint.iacr.org/2023/1217.pdf) - Section on sumcheck
- [Justin Thaler's Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) - Chapter 4

---

**Happy Learning! 🚀**

These examples show you the power of sumcheck - the foundation of modern zkVMs!
