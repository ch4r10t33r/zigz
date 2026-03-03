const std = @import("std");
const zigz = @import("zigz");

/// End-to-End Prover and Verifier Demo
///
/// This example demonstrates the complete zkVM workflow:
/// 1. Write a simple RISC-V program
/// 2. Generate a proof of execution
/// 3. Verify the proof
///
/// This showcases the security fixes from Phase 9:
/// - Proper Fiat-Shamir transcript binding
/// - Two-phase polynomial commitment protocol
/// - Domain separation to prevent cross-protocol attacks

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    std.debug.print("\n=== zigz zkVM: Prover + Verifier Demo ===\n\n", .{});

    // Use BabyBear field for efficiency
    const F = zigz.BabyBear;

    // ========================================================================
    // STEP 1: Create a simple RISC-V program
    // ========================================================================

    std.debug.print("Step 1: Creating test program...\n", .{});

    // Simple program that adds two numbers
    // x1 = 5, x2 = 10, x3 = x1 + x2 (should be 15)
    const program = [_]u8{
        // ADDI x1, x0, 5     (x1 = 5)
        0x93, 0x00, 0x50, 0x00,
        // ADDI x2, x0, 10    (x2 = 10)
        0x13, 0x01, 0xA0, 0x00,
        // ADD x3, x1, x2     (x3 = x1 + x2)
        0xB3, 0x01, 0x20, 0x00,
        // ADDI x0, x0, 0     (NOP - halt)
        0x13, 0x00, 0x00, 0x00,
    };

    const entry_pc: u64 = 0x1000;

    std.debug.print("  Program size: {d} bytes\n", .{program.len});
    std.debug.print("  Entry PC: 0x{X:0>8}\n\n", .{entry_pc});

    // ========================================================================
    // STEP 2: Generate proof (PROVER)
    // ========================================================================

    std.debug.print("Step 2: Generating proof...\n", .{});

    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    const start_time = std.time.milliTimestamp();

    var proof = try prover.prove(&program, entry_pc, null);
    defer proof.deinit();

    const prove_time_ms = std.time.milliTimestamp() - start_time;

    std.debug.print("  Proof generated in {d} ms\n", .{prove_time_ms});
    std.debug.print("  Proof size: ~{d} bytes\n", .{proof.estimateSize()});
    std.debug.print("  Number of execution steps: {d}\n", .{proof.metadata.num_steps});
    std.debug.print("  Number of variables (log2 steps): {d}\n", .{proof.metadata.num_vars});
    std.debug.print("  Witness polynomials: {d}\n", .{proof.witness_commitments.len});
    std.debug.print("  Lookup tables used: {d}\n\n", .{proof.lookup_proofs.items.len});

    // Display public outputs
    std.debug.print("  Public outputs:\n", .{});
    std.debug.print("    Initial PC: 0x{X:0>8}\n", .{proof.public_io.initial_pc});
    std.debug.print("    Final PC: 0x{X:0>8}\n", .{proof.public_io.final_pc});

    if (proof.public_io.final_regs) |regs| {
        std.debug.print("    Final registers:\n", .{});
        for (regs, 0..) |reg, i| {
            if (reg != 0) {
                std.debug.print("      x{d} = {d}\n", .{ i, reg });
            }
        }
    }

    std.debug.print("\n", .{});

    // ========================================================================
    // STEP 3: Serialize proof (optional - for storage/transmission)
    // ========================================================================

    std.debug.print("Step 3: Serializing proof...\n", .{});

    const serializer = zigz.serialization.BinarySerializer(F);
    const proof_bytes = try serializer.serialize(allocator, proof);
    defer allocator.free(proof_bytes);

    std.debug.print("  Serialized size: {d} bytes\n", .{proof_bytes.len});
    std.debug.print("  Compression ratio: {d:.2}x\n\n", .{
        @as(f64, @floatFromInt(proof.estimateSize())) / @as(f64, @floatFromInt(proof_bytes.len)),
    });

    // ========================================================================
    // STEP 4: Deserialize proof (simulate receiving proof)
    // ========================================================================

    std.debug.print("Step 4: Deserializing proof...\n", .{});

    var deserialized_proof = try serializer.deserialize(allocator, proof_bytes);
    defer deserialized_proof.deinit();

    std.debug.print("  Proof deserialized successfully\n\n", .{});

    // ========================================================================
    // STEP 5: Verify proof (VERIFIER)
    // ========================================================================

    std.debug.print("Step 5: Verifying proof...\n", .{});

    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const verify_start_time = std.time.milliTimestamp();

    const result = try verifier.verify(deserialized_proof, &program);

    const verify_time_ms = std.time.milliTimestamp() - verify_start_time;

    std.debug.print("  Verification completed in {d} ms\n", .{verify_time_ms});
    std.debug.print("  Result: {s}\n\n", .{@tagName(result)});

    // ========================================================================
    // STEP 6: Display results and security properties
    // ========================================================================

    std.debug.print("=== Security Properties ===\n\n", .{});

    std.debug.print("✓ Fiat-Shamir transcript properly bound:\n", .{});
    std.debug.print("  - Public inputs bound BEFORE any challenges\n", .{});
    std.debug.print("  - All polynomial commitments bound BEFORE opening challenges\n", .{});
    std.debug.print("  - Domain separators prevent cross-protocol attacks\n\n", .{});

    std.debug.print("✓ Two-phase commitment protocol:\n", .{});
    std.debug.print("  - Phase 1: Generate all commitments (Merkle roots)\n", .{});
    std.debug.print("  - Phase 2: Bind all commitments to transcript\n", .{});
    std.debug.print("  - Phase 3: Derive opening challenges from transcript\n\n", .{});

    std.debug.print("✓ Prevents 'unfaithful claims' vulnerability:\n", .{});
    std.debug.print("  - Sumcheck input claims bound to transcript\n", .{});
    std.debug.print("  - Batching coefficients αi depend on all claims Hi\n", .{});
    std.debug.print("  - Verification equation no longer linear in manipulable claims\n\n", .{});

    // ========================================================================
    // STEP 7: Performance summary
    // ========================================================================

    std.debug.print("=== Performance Summary ===\n\n", .{});

    std.debug.print("Prover time: {d} ms\n", .{prove_time_ms});
    std.debug.print("Verifier time: {d} ms ({d:.1f}x faster)\n", .{
        verify_time_ms,
        @as(f64, @floatFromInt(prove_time_ms)) / @as(f64, @floatFromInt(verify_time_ms)),
    });
    std.debug.print("Proof size: {d} bytes\n", .{proof_bytes.len});
    std.debug.print("Verification complexity: O(log n) = O({d})\n\n", .{proof.metadata.num_vars});

    if (result == .Accept) {
        std.debug.print("✓ Proof verified successfully!\n\n", .{});
        return;
    } else {
        std.debug.print("✗ Proof verification failed: {s}\n\n", .{@tagName(result)});
        return error.VerificationFailed;
    }
}
