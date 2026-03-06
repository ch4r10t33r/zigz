const std = @import("std");
const testing = std.testing;
const zigz = @import("zigz");

/// Integration tests for zigz zkVM
///
/// These tests verify the complete prover-verifier workflow:
/// 1. Execute RISC-V program
/// 2. Generate proof of execution
/// 3. Verify proof
/// 4. Test security properties
///
/// Tests cover:
/// - Basic correctness (valid proofs accept)
/// - Security (tampered proofs reject)
/// - Different program sizes
/// - Serialization roundtrip
/// - Fiat-Shamir binding order
const F = zigz.BabyBear;

// Helper to create simple test programs
fn createNOPProgram(allocator: std.mem.Allocator, num_instructions: usize) ![]u8 {
    const program = try allocator.alloc(u8, num_instructions * 4);
    // Fill with NOP (ADDI x0, x0, 0 = 0x00000013)
    for (0..num_instructions) |i| {
        const offset = i * 4;
        program[offset + 0] = 0x13;
        program[offset + 1] = 0x00;
        program[offset + 2] = 0x00;
        program[offset + 3] = 0x00;
    }
    return program;
}

fn createAddProgram(allocator: std.mem.Allocator) ![]u8 {
    // Simple program that adds two numbers
    // x1 = 5, x2 = 10, x3 = x1 + x2
    const program = [_]u8{
        // ADDI x1, x0, 5     (x1 = 5)
        0x93, 0x00, 0x50, 0x00,
        // ADDI x2, x0, 10    (x2 = 10)
        0x13, 0x01, 0xA0, 0x00,
        // ADD x3, x1, x2     (x3 = x1 + x2 = 15)
        0xB3, 0x01, 0x20, 0x00,
        // ADDI x0, x0, 0     (NOP - halt)
        0x13, 0x00, 0x00, 0x00,
    };
    return allocator.dupe(u8, &program);
}

// ============================================================================
// Test 1: Basic End-to-End (Valid Proof Acceptance)
// ============================================================================

test "integration: basic end-to-end proof verification" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Basic End-to-End ===\n", .{});

    // Create simple program
    const program = try createAddProgram(allocator);
    defer allocator.free(program);
    const entry_pc: u64 = 0x1000;

    // Generate proof
    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
    defer proof.deinit();

    std.debug.print("Proof generated: {d} steps\n", .{proof.metadata.num_steps});

    // Verify proof
    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const result = try verifier.verify(proof, program);

    std.debug.print("Verification result: {s}\n", .{@tagName(result)});

    // Should accept valid proof
    try testing.expectEqual(zigz.proof.VerificationResult.Accept, result);
}

// ============================================================================
// Test 2: Serialization Roundtrip
// ============================================================================

test "integration: serialization roundtrip preserves proof validity" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Serialization Roundtrip ===\n", .{});

    const program = try createAddProgram(allocator);
    defer allocator.free(program);
    const entry_pc: u64 = 0x1000;

    // Generate proof
    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
    defer proof.deinit();

    // Serialize
    const serializer = zigz.serialization.BinarySerializer(F);
    const proof_bytes = try serializer.serialize(allocator, proof);
    defer allocator.free(proof_bytes);

    std.debug.print("Serialized proof: {d} bytes\n", .{proof_bytes.len});

    // Deserialize
    var deserialized_proof = try serializer.deserialize(allocator, proof_bytes);
    defer deserialized_proof.deinit();

    // Verify deserialized proof
    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const result = try verifier.verify(deserialized_proof, program);

    std.debug.print("Verification after roundtrip: {s}\n", .{@tagName(result)});

    // Should still accept after serialization roundtrip
    try testing.expectEqual(zigz.proof.VerificationResult.Accept, result);
}

// ============================================================================
// Test 3: Program Hash Verification
// ============================================================================

test "integration: wrong program hash causes rejection" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Program Hash Mismatch ===\n", .{});

    const program = try createAddProgram(allocator);
    defer allocator.free(program);
    const entry_pc: u64 = 0x1000;

    // Generate proof for original program
    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
    defer proof.deinit();

    // Try to verify with different program
    const different_program = try createNOPProgram(allocator, 4);
    defer allocator.free(different_program);

    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    // Should fail with program hash mismatch
    const result = verifier.verify(proof, different_program);

    std.debug.print("Result with wrong program: {s}\n", .{
        if (result) |r| @tagName(r) else |e| @errorName(e),
    });

    // Should error due to program hash mismatch
    try testing.expectError(error.ProgramHashMismatch, result);
}

// ============================================================================
// Test 4: Different Program Sizes
// ============================================================================

test "integration: various program sizes verify correctly" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Various Program Sizes ===\n", .{});

    const test_sizes = [_]usize{ 4, 8, 16, 32 };

    for (test_sizes) |size| {
        std.debug.print("Testing program with {d} instructions...\n", .{size});

        const program = try createNOPProgram(allocator, size);
        defer allocator.free(program);

        const entry_pc: u64 = 0x1000;

        // Generate proof
        var prover = try zigz.Prover(F).init(allocator, 0);
        defer prover.deinit();

        var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
        defer proof.deinit();

        std.debug.print("  Proof size: ~{d} bytes\n", .{proof.estimateSize()});
        std.debug.print("  Variables: {d}\n", .{proof.metadata.num_vars});

        // Verify proof
        var verifier = zigz.Verifier(F).init(allocator);
        defer verifier.deinit();

        const result = try verifier.verify(proof, program);

        try testing.expectEqual(zigz.proof.VerificationResult.Accept, result);
    }

    std.debug.print("All sizes verified successfully!\n", .{});
}

// ============================================================================
// Test 5: Transcript Determinism
// ============================================================================

test "integration: transcript generates deterministic challenges" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Transcript Determinism ===\n", .{});

    const program = try createAddProgram(allocator);
    defer allocator.free(program);
    const entry_pc: u64 = 0x1000;

    // Generate two proofs with same inputs
    var prover1 = try zigz.Prover(F).init(allocator, 0);
    defer prover1.deinit();

    var proof1 = try prover1.prove(program, entry_pc, null, 1 << 20, null);
    defer proof1.deinit();

    var prover2 = try zigz.Prover(F).init(allocator, 0);
    defer prover2.deinit();

    var proof2 = try prover2.prove(program, entry_pc, null, 1 << 20, null);
    defer proof2.deinit();

    // Transcripts should generate same challenges
    // Check that opening points are identical (derived from transcript)
    for (proof1.witness_commitments, proof2.witness_commitments, 0..) |c1, c2, i| {
        std.debug.print("Commitment {d} opening point comparison:\n", .{i});
        for (c1.point, c2.point, 0..) |p1, p2, j| {
            std.debug.print("  Coord {d}: {d} vs {d}\n", .{ j, p1.value, p2.value });
            try testing.expect(p1.eql(p2));
        }
    }

    std.debug.print("Transcripts are deterministic!\n", .{});
}

// ============================================================================
// Test 6: Security - Tampered Commitment Rejection
// ============================================================================

test "integration: tampered commitment causes rejection" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Tampered Commitment ===\n", .{});

    const program = try createAddProgram(allocator);
    defer allocator.free(program);
    const entry_pc: u64 = 0x1000;

    // Generate valid proof
    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
    defer proof.deinit();

    // Tamper with a commitment
    if (proof.witness_commitments.len > 0) {
        std.debug.print("Tampering with commitment[0]...\n", .{});
        proof.witness_commitments[0].commitment[0] ^= 0xFF; // Flip bits
    }

    // Try to verify tampered proof
    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const result = try verifier.verify(proof, program);

    std.debug.print("Verification of tampered proof: {s}\n", .{@tagName(result)});

    // Should reject tampered proof
    try testing.expect(result != .Accept);
}

// ============================================================================
// Test 7: Security - Opening Claim Binding (Jolt PR #981)
// ============================================================================

test "integration: opening claims are bound to transcript" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Opening Claims Binding ===\n", .{});

    const program = try createAddProgram(allocator);
    defer allocator.free(program);
    const entry_pc: u64 = 0x1000;

    // Generate proof
    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
    defer proof.deinit();

    // Tamper with an opening claim (evaluation value)
    if (proof.witness_commitments.len > 0) {
        std.debug.print("Tampering with opening claim value...\n", .{});
        const original_value = proof.witness_commitments[0].value;
        // Change the claim to a different value
        proof.witness_commitments[0].value = original_value.add(F.one());

        std.debug.print("Original: {d}, Tampered: {d}\n", .{
            original_value.value,
            proof.witness_commitments[0].value.value,
        });
    }

    // Try to verify with tampered claim
    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const result = try verifier.verify(proof, program);

    std.debug.print("Verification with tampered claim: {s}\n", .{@tagName(result)});

    // Should reject because claim binding will cause transcript divergence
    // The verifier will derive different challenges than the prover
    try testing.expect(result != .Accept);
}

// ============================================================================
// Test 8: Public Input Binding
// ============================================================================

test "integration: public inputs bound to transcript" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Public Input Binding ===\n", .{});

    const program = try createAddProgram(allocator);
    defer allocator.free(program);

    // Generate two proofs with different initial PCs
    var prover1 = try zigz.Prover(F).init(allocator, 0);
    defer prover1.deinit();

    var proof1 = try prover1.prove(program, 0x1000, null, 1 << 20, null);
    defer proof1.deinit();

    var prover2 = try zigz.Prover(F).init(allocator, 0);
    defer prover2.deinit();

    var proof2 = try prover2.prove(program, 0x2000, null, 1 << 20, null);
    defer proof2.deinit();

    // Proofs should be different because initial PC is bound to transcript
    std.debug.print("Proof 1 initial PC: 0x{X}\n", .{proof1.public_io.initial_pc});
    std.debug.print("Proof 2 initial PC: 0x{X}\n", .{proof2.public_io.initial_pc});

    // Check that at least one opening point differs (due to different transcript)
    var points_differ = false;
    if (proof1.witness_commitments.len > 0 and proof2.witness_commitments.len > 0) {
        for (proof1.witness_commitments[0].point, proof2.witness_commitments[0].point) |p1, p2| {
            if (!p1.eql(p2)) {
                points_differ = true;
                break;
            }
        }
    }

    std.debug.print("Opening points differ due to PC binding: {}\n", .{points_differ});

    // Different initial PCs should lead to different transcript state
    try testing.expect(points_differ);
}

// ============================================================================
// Test 9: Proof Size Scaling (Should be O(log n))
// ============================================================================

test "integration: proof size scales logarithmically" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Proof Size Scaling ===\n", .{});

    const test_sizes = [_]usize{ 4, 8, 16, 32, 64 };
    var proof_sizes = std.ArrayList(usize){};
    defer proof_sizes.deinit(allocator);

    for (test_sizes) |size| {
        const program = try createNOPProgram(allocator, size);
        defer allocator.free(program);

        var prover = try zigz.Prover(F).init(allocator, 0);
        defer prover.deinit();

        var proof = try prover.prove(program, 0x1000, null, 1 << 20, null);
        defer proof.deinit();

        const proof_size = proof.estimateSize();
        try proof_sizes.append(allocator, proof_size);

        std.debug.print("{d:4} steps → {d:6} bytes ({d} vars)\n", .{
            size,
            proof_size,
            proof.metadata.num_vars,
        });
    }

    // Check that doubling steps doesn't double proof size
    // For O(log n), doubling n should add constant size
    for (1..proof_sizes.items.len) |i| {
        const prev_size = @as(f64, @floatFromInt(proof_sizes.items[i - 1]));
        const curr_size = @as(f64, @floatFromInt(proof_sizes.items[i]));
        const size_ratio = curr_size / prev_size;

        std.debug.print("Size ratio for 2x steps: {d:.2}\n", .{size_ratio});

        // Should be less than 2x (sublinear)
        try testing.expect(size_ratio < 2.0);
    }

    std.debug.print("Proof size scaling is sublinear (O(log n))!\n", .{});
}

// ============================================================================
// Test 10: Performance Benchmark
// ============================================================================

test "integration: performance benchmark" {
    const allocator = testing.allocator;

    std.debug.print("\n=== Test: Performance Benchmark ===\n", .{});

    const program = try createNOPProgram(allocator, 64);
    defer allocator.free(program);

    const entry_pc: u64 = 0x1000;

    // Measure proving time
    var timer = try std.time.Timer.start();

    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    var proof = try prover.prove(program, entry_pc, null, 1 << 20, null);
    defer proof.deinit();

    const prove_time_ns = timer.read();
    const prove_time_ms = @as(f64, @floatFromInt(prove_time_ns)) / 1_000_000.0;

    std.debug.print("Proving time: {d:.2} ms\n", .{prove_time_ms});

    // Measure verification time
    timer.reset();

    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const result = try verifier.verify(proof, program);

    const verify_time_ns = timer.read();
    const verify_time_ms = @as(f64, @floatFromInt(verify_time_ns)) / 1_000_000.0;

    std.debug.print("Verification time: {d:.2} ms\n", .{verify_time_ms});
    std.debug.print("Speedup: {d:.1}x\n", .{prove_time_ms / verify_time_ms});

    try testing.expectEqual(zigz.proof.VerificationResult.Accept, result);

    // Verification should be significantly faster than proving
    try testing.expect(verify_time_ns < prove_time_ns);
}
