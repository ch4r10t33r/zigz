# Integration Tests

This directory contains comprehensive integration tests for the zigz zkVM that verify the complete prover-verifier workflow.

## Overview

Integration tests verify that:
1. **Valid proofs are accepted** - Correct execution traces produce verifiable proofs
2. **Invalid proofs are rejected** - Tampered proofs fail verification
3. **Security properties hold** - Fiat-Shamir vulnerabilities are prevented
4. **Performance scales correctly** - Proof size and verification time are O(log n)

## Test Suite

### Test 1: Basic End-to-End
**Purpose**: Verify the fundamental prover-verifier workflow

**What it does**:
- Creates a simple RISC-V program (adds two numbers)
- Generates a proof of execution
- Verifies the proof
- Expects: Accept

**Why it matters**: This is the most basic correctness check. If this fails, nothing else matters.

### Test 2: Serialization Roundtrip
**Purpose**: Verify proof serialization preserves validity

**What it does**:
- Generates a proof
- Serializes to bytes
- Deserializes back to proof structure
- Verifies the deserialized proof
- Expects: Accept

**Why it matters**: Real-world zkVMs need to serialize proofs for storage/transmission. This verifies that serialization doesn't corrupt the proof.

### Test 3: Program Hash Verification
**Purpose**: Verify proof is bound to specific program

**What it does**:
- Generates proof for program A
- Attempts to verify with program B
- Expects: ProgramHashMismatch error

**Why it matters**: Prevents proof reuse attacks where an attacker uses a valid proof for one program to claim execution of a different program.

### Test 4: Various Program Sizes
**Purpose**: Verify correctness across different execution lengths

**What it does**:
- Tests programs with 4, 8, 16, 32 instructions
- Generates and verifies proofs for each
- Expects: All accept

**Why it matters**: Ensures the zkVM works correctly for different trace lengths, not just edge cases.

### Test 5: Transcript Determinism
**Purpose**: Verify Fiat-Shamir challenges are deterministic

**What it does**:
- Generates two proofs with identical inputs
- Compares opening points (derived from transcript)
- Expects: Identical challenges

**Why it matters**: Fiat-Shamir transformation requires deterministic challenge generation. Non-determinism would make proofs non-reproducible.

### Test 6: Tampered Commitment Rejection
**Purpose**: Verify commitment tampering is detected

**What it does**:
- Generates valid proof
- Tampers with a Merkle root commitment
- Attempts verification
- Expects: Rejection

**Why it matters**: Ensures the commitment scheme provides binding - prover cannot change committed values without detection.

### Test 7: Opening Claims Binding (Jolt PR #981)
**Purpose**: Verify the critical security fix for unfaithful claims

**What it does**:
- Generates valid proof
- Tampers with an opening claim value (polynomial evaluation)
- Attempts verification
- Expects: Rejection (due to transcript divergence)

**Why it matters**: This is the **most critical security test**. It verifies that opening claims (Hi) are bound to the Fiat-Shamir transcript BEFORE batching coefficients are derived.

**The vulnerability** (if not fixed):
```
BatchedClaim = Σ αi · Hi
```
If Hi values are NOT in transcript when deriving αi, then αi is independent of Hi, making verification linear:
```
C_final = a·H + b = expected_eval
```
An attacker can solve this small linear system for fake claims.

**The fix** (implemented in Phase 4):
```zig
// Bind all opening claims to transcript
self.transcript.appendBytes("OPENING_CLAIMS");
for (proof.witness_commitments) |commitment| {
    self.transcript.appendFieldElement(F, commitment.value);
}
```

Now αi depends on all Hi, preventing manipulation.

### Test 8: Public Input Binding
**Purpose**: Verify public inputs affect transcript state

**What it does**:
- Generates two proofs with different initial PCs
- Compares opening points
- Expects: Different opening points (due to different transcript)

**Why it matters**: Ensures public inputs are bound to the transcript BEFORE deriving challenges. Otherwise, an attacker could use the same proof for different public inputs.

### Test 9: Proof Size Scaling
**Purpose**: Verify proof size grows logarithmically

**What it does**:
- Tests programs with 4, 8, 16, 32, 64 instructions
- Measures proof size for each
- Checks that doubling steps doesn't double proof size
- Expects: Size ratio < 2.0 (sublinear)

**Why it matters**: O(log n) proof size is a key zkVM efficiency metric. Linear growth would make the system impractical for large programs.

**Expected behavior**:
- 4 steps → ~X bytes
- 8 steps → ~X + ΔX bytes (NOT 2X)
- 16 steps → ~X + 2ΔX bytes (NOT 4X)

### Test 10: Performance Benchmark
**Purpose**: Measure and verify prover/verifier performance

**What it does**:
- Measures proving time
- Measures verification time
- Compares speedup
- Expects: Verification significantly faster than proving

**Why it matters**: The whole point of zkVMs is to make verification cheaper than re-execution. This verifies that property holds.

**Expected ratios**:
- Prover time: ~100ms for 64 instructions
- Verifier time: ~1ms for 64 instructions
- Speedup: ~100x (verification faster)

## Running Tests

### Run Integration Tests Only
```bash
zig build test-integration
```

### Run All Tests (Unit + Integration)
```bash
zig build test-all
```

### Run with Verbose Output
```bash
zig build test-integration -- --verbose
```

## Test Output

Tests print detailed progress information:

```
=== Test: Basic End-to-End ===
Proof generated: 4 steps
Verification result: Accept

=== Test: Opening Claims Binding ===
Tampering with opening claim value...
Original: 42, Tampered: 43
Verification with tampered claim: RejectInvalidCommitment
```

## Security Test Importance

The integration tests include **critical security checks** that verify the Fiat-Shamir fixes from Phase 9:

### Why These Tests Matter

1. **Test 6 (Tampered Commitment)**: Prevents prover from changing committed polynomials
2. **Test 7 (Opening Claims Binding)**: Prevents the Jolt PR #981 vulnerability
3. **Test 8 (Public Input Binding)**: Prevents proof reuse across different inputs

**If any of these fail, the zkVM is insecure!**

## Adding New Tests

When adding new tests, follow this pattern:

```zig
test "integration: descriptive test name" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Name ===\n", .{});

    // Setup
    const program = // ... create test program

    // Generate proof
    var prover = try zigz.Prover(F).init(allocator);
    defer prover.deinit();
    var proof = try prover.prove(program, entry_pc, null);
    defer proof.deinit();

    // Test-specific logic
    // ...

    // Verify
    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();
    const result = try verifier.verify(proof, program);

    // Assertions
    try testing.expectEqual(expected_result, result);
}
```

## Performance Expectations

Based on the BabyBear field and Merkle tree commitments:

| Steps | Proof Size | Prove Time | Verify Time |
|-------|-----------|------------|-------------|
| 4     | ~5 KB     | ~10 ms     | ~0.1 ms     |
| 16    | ~10 KB    | ~30 ms     | ~0.3 ms     |
| 64    | ~20 KB    | ~100 ms    | ~1 ms       |
| 256   | ~40 KB    | ~400 ms    | ~3 ms       |

Actual times will vary based on hardware and optimization level.

## Debugging Failed Tests

If tests fail:

1. **Check verbose output**: Run with `--verbose` flag
2. **Verify compilation**: Run `zig build` first to catch compilation errors
3. **Check allocator**: Memory leaks will cause test failures
4. **Review transcript binding**: Most failures relate to incorrect Fiat-Shamir order

## Common Issues

### "ProgramHashMismatch" in valid tests
- **Cause**: Program was modified after proof generation
- **Fix**: Ensure program bytes are not modified between prove() and verify()

### "RejectInvalidCommitment" in valid tests
- **Cause**: Transcript binding order mismatch between prover and verifier
- **Fix**: Verify prover and verifier use identical transcript.appendBytes() calls in same order

### "OutOfMemory" errors
- **Cause**: Large programs without proper cleanup
- **Fix**: Ensure all allocations have matching defer statements

## References

- [Jolt zkVM Paper](https://eprint.iacr.org/2023/1217)
- [Unfaithful Claims Vulnerability](https://osec.io/blog/2026-03-03-zkvms-unfaithful-claims/)
- [Fiat-Shamir Transform](https://en.wikipedia.org/wiki/Fiat%E2%80%93Shamir_heuristic)
- [Integration Testing Best Practices](https://martinfowler.com/bliki/IntegrationTest.html)
