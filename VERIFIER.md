# zigz Verifier Implementation

## Overview

The zigz verifier implements **Phase 9** of the implementation plan: a complete zero-knowledge proof verifier for RISC-V program execution. The verifier can check proofs in **O(log n)** time without access to the execution trace.

## Architecture

### Core Components

1. **`src/verifier/verifier.zig`** - Main verification logic
   - Transcript management with proper Fiat-Shamir binding
   - Sumcheck proof verification
   - Lasso lookup verification
   - Polynomial opening verification

2. **`src/verifier/benchmarks.zig`** - Performance measurement
   - Verification time scaling analysis
   - Proof size analysis
   - Throughput measurement

3. **`examples/prover_verifier_demo.zig`** - End-to-end demo
   - Complete workflow from program → proof → verification
   - Security property demonstration
   - Performance summary

## Security Fixes (Critical)

The verifier implementation includes comprehensive security fixes to prevent the **"unfaithful claims"** vulnerability that affected Jolt zkVM (see [osec.io blog post](https://osec.io/blog/2026-03-03-zkvms-unfaithful-claims/)).

### The Vulnerability

In the original Jolt implementation, sumcheck input claims (the `opening_claims` values) were **not bound to the Fiat-Shamir transcript** before deriving batching coefficients. This created a critical vulnerability:

```
BatchedClaim = Σ αi · Hi
```

Where:
- `Hi` are the sumcheck input claims (NOT in transcript)
- `αi` are batching coefficients (derived from transcript)

Since `αi` is independent of `Hi`, the final verification equation becomes **linear** in the unbound claim `H`:

```
C_final = a·H + b = expected_eval
```

Where `a` and `b` are determined by the transcript (independent of `H`). An attacker can solve this small linear system to find a fake claim `H` that passes verification.

### Our Fixes

We implement **five critical security measures**:

#### 1. Public Input Binding (Phase 1)

**ALL** public inputs must be bound to the transcript **BEFORE** deriving any challenges:

```zig
// CRITICAL: Bind all public inputs to transcript FIRST
var program_hash: [32]u8 = undefined;
std.crypto.hash.sha2.Sha256.hash(program, &program_hash, .{});
self.transcript.appendBytes(&program_hash);
self.transcript.appendFieldElement(F, F.init(entry_pc));

if (initial_regs) |regs| {
    for (regs) |reg_val| {
        self.transcript.appendFieldElement(F, F.init(reg_val));
    }
}
```

#### 2. Two-Phase Commitment Protocol (Phase 2)

Polynomial commitments are handled in **three distinct phases**:

```zig
// PHASE 1: Generate commitments (Merkle roots only)
for (polynomials, 0..) |poly, i| {
    var committer = try polynomial_commit.PolynomialCommitter(F).init(self.allocator);
    defer committer.deinit();
    const commitment = try committer.commit(poly);
    proof.witness_commitments[i].commitment = commitment;
}

// PHASE 2: Bind all commitments to transcript (CRITICAL!)
self.transcript.appendBytes("POLY_COMMITMENTS");
for (proof.witness_commitments) |commitment| {
    self.transcript.appendBytes(&commitment.commitment);
}

// PHASE 3: Derive opening challenges from transcript
for (polynomials, 0..) |poly, i| {
    for (proof.witness_commitments[i].point, 0..) |*coord, j| {
        coord.* = self.transcript.challenge(F); // From transcript, NOT random
    }
    proof.witness_commitments[i].value = try poly.evaluate(proof.witness_commitments[i].point);
}
```

This ensures that:
- All commitments are visible to the attacker BEFORE challenges are derived
- Batching coefficients `αi` **depend on all claims** `Hi`
- The verification equation is no longer linear in manipulable claims

#### 3. Domain Separation

Every protocol phase has a unique domain separator to prevent cross-protocol attacks:

```zig
// Sumcheck protocol
self.transcript.appendBytes("SUMCHECK_BEGIN");
self.transcript.appendFieldElement(F, F.init(witness.num_steps));
self.transcript.appendFieldElement(F, F.init(num_vars));

// Lasso lookup arguments
self.transcript.appendBytes("LASSO_BEGIN");
// For each table:
self.transcript.appendBytes("LASSO_TABLE");
self.transcript.appendFieldElement(F, F.init(table_id));

// Polynomial commitments
self.transcript.appendBytes("POLY_COMMITMENTS");
```

#### 4. Fresh Transcript Per Proof

Each proof generation starts with a fresh transcript to prevent state leakage:

```zig
pub fn prove(...) !Proof {
    // SECURITY: Initialize fresh Fiat-Shamir transcript for this proof
    self.transcript = hash.FiatShamirTranscript.init();

    // ... rest of proof generation
}
```

#### 5. Deterministic Challenge Derivation

All challenges are derived from the transcript, NOT from independent randomness:

```zig
// SECURITY FIX: Derive evaluation point from Fiat-Shamir transcript
// NOT from independent random generator
for (opening.point, 0..) |*coord, i| {
    coord.* = self.transcript.challenge(F);  // Changed from self.rng.int()
}
```

## Verification Workflow

### Step-by-Step Process

1. **Initialize Transcript**
   ```zig
   self.transcript = hash.FiatShamirTranscript.init();
   ```

2. **Bind Public Inputs** (must match prover order exactly)
   ```zig
   self.transcript.appendBytes(&program_hash);
   self.transcript.appendFieldElement(F, F.init(initial_pc));
   // ... bind all initial registers
   ```

3. **Bind Polynomial Commitments** (all at once)
   ```zig
   self.transcript.appendBytes("POLY_COMMITMENTS");
   for (commitments) |commitment| {
       self.transcript.appendBytes(&commitment.commitment);
   }
   ```

4. **Verify Sumcheck Proof**
   - Check round polynomial properties: `g(0) + g(1) = claimed_sum`
   - Derive challenges from transcript
   - Verify final evaluation

5. **Verify Lasso Lookup Proofs**
   - Verify multiset equality via sumcheck
   - Check subtable proofs if present

6. **Verify Polynomial Openings**
   - Derive evaluation points from transcript
   - Verify Merkle authentication paths
   - Check claimed evaluations

7. **Accept or Reject**
   - Accept if all checks pass
   - Return specific rejection reason otherwise

## Performance Characteristics

### Complexity

- **Verification time**: O(log n) where n = number of execution steps
- **Proof size**: O(log n) field elements
- **Memory**: O(log n)

### Expected Performance

For a program with **1024 execution steps** (10 variables):
- Proof size: ~10-50 KB
- Verification time: < 1 second
- Prover/verifier ratio: ~100-1000x (verifier much faster)

### Scaling

Doubling the number of steps adds only **constant time** to verification:

| Steps | Variables | Expected Verify Time |
|-------|-----------|----------------------|
| 16    | 4         | ~100 μs              |
| 64    | 6         | ~150 μs              |
| 256   | 8         | ~200 μs              |
| 1024  | 10        | ~250 μs              |
| 4096  | 12        | ~300 μs              |

## Testing

### Unit Tests

Run verifier unit tests:
```bash
zig build test-verifier
```

Tests cover:
- Initialization and cleanup
- Public input binding order (critical for security)
- Transcript determinism (same inputs → same challenges)
- Sumcheck verification logic
- Lasso verification logic
- Polynomial opening verification

### Benchmarks

Run performance benchmarks:
```bash
zig build bench
```

Benchmarks measure:
- Verification time vs. number of steps
- Proof size growth (should be logarithmic)
- Throughput (steps verified per second)
- Scaling analysis (verify O(log n) complexity)

### End-to-End Demo

Run complete prover → verifier workflow:
```bash
zig build
./zig-out/bin/prover_verifier_demo
```

This demonstrates:
- Program execution
- Proof generation with security fixes
- Proof serialization
- Proof deserialization
- Verification with proper transcript binding
- Security property validation

## Integration with Prover

### Critical: Transcript Binding Order

The verifier **MUST** replicate the exact transcript binding order used by the prover. Any deviation will cause verification to fail, even for valid proofs.

**Prover order** (from `src/prover/prover.zig`):
1. Public inputs (program hash, PC, registers)
2. Domain separator: `"POLY_COMMITMENTS"`
3. All polynomial commitments
4. Domain separator: `"SUMCHECK_BEGIN"`
5. Sumcheck metadata (num_steps, num_vars)
6. Sumcheck rounds (bind each evaluation)
7. Domain separator: `"LASSO_BEGIN"` + `"LASSO_TABLE"` per table
8. Lasso proofs (one per table)

**Verifier order** (from `src/verifier/verifier.zig`):
- **MUST MATCH PROVER EXACTLY**

### Challenge Derivation

Both prover and verifier use the same method:
```zig
const challenge = self.transcript.challenge(F);
```

This ensures deterministic, verifiable randomness without interaction.

## API Usage

### Basic Verification

```zig
const std = @import("std");
const zigz = @import("zigz");

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    // Load proof and program
    const proof = // ... load serialized proof
    const program = // ... load program bytes

    // Create verifier
    var verifier = zigz.Verifier(zigz.BabyBear).init(allocator);
    defer verifier.deinit();

    // Verify
    const result = try verifier.verify(proof, program);

    if (result == .Accept) {
        std.debug.print("Proof verified!\n", .{});
    } else {
        std.debug.print("Verification failed: {s}\n", .{@tagName(result)});
    }
}
```

### With Error Handling

```zig
const result = verifier.verify(proof, program) catch |err| {
    switch (err) {
        error.ProgramHashMismatch => {
            std.debug.print("Program hash doesn't match!\n", .{});
        },
        else => {
            std.debug.print("Verification error: {s}\n", .{@errorName(err)});
        },
    }
    return err;
};

switch (result) {
    .Accept => std.debug.print("✓ Valid proof\n", .{}),
    .RejectInvalidSumcheck => std.debug.print("✗ Sumcheck failed\n", .{}),
    .RejectInvalidLookup => std.debug.print("✗ Lookup failed\n", .{}),
    .RejectInvalidCommitment => std.debug.print("✗ Commitment failed\n", .{}),
    .RejectInvalidPublicIO => std.debug.print("✗ Public IO mismatch\n", .{}),
}
```

## Next Steps

With Phase 9 complete, the zkVM has:
- ✅ Full prover implementation
- ✅ Full verifier implementation
- ✅ Security fixes for Fiat-Shamir vulnerabilities
- ✅ O(log n) proof size and verification time
- ✅ End-to-end testing and benchmarks

**Remaining work** (Phase 10):
- Integration testing with real RISC-V programs
- Performance optimization (field arithmetic, caching)
- Extended ISA support (RV64I, M extension, etc.)
- Proof compression and recursion
- Production hardening

## References

- [Jolt zkVM Paper](https://eprint.iacr.org/2023/1217)
- [Lasso Lookup Arguments](https://eprint.iacr.org/2023/1216)
- [Fiat-Shamir Unfaithful Claims Vulnerability](https://osec.io/blog/2026-03-03-zkvms-unfaithful-claims/)
- [Sumcheck Protocol](https://people.cs.georgetown.edu/jthaler/sumcheck.pdf)
- [RISC-V ISA Specification](https://riscv.org/technical/specifications/)
