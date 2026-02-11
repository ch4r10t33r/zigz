/// Sumcheck for Constraint Verification
///
/// This example shows how sumcheck is used to prove constraints in a zkVM.
/// Demonstrates proving that a computation was done correctly.
///
/// Example: Prove that for all steps, output = input1 + input2 (addition constraint)

const std = @import("std");
const field_presets = @import("../src/core/field_presets.zig");
const multilinear = @import("../src/poly/multilinear.zig");
const prover_module = @import("../src/proofs/sumcheck_prover.zig");
const verifier_module = @import("../src/proofs/sumcheck_verifier.zig");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const stdout = std.io.getStdOut().writer();

    try stdout.writeAll("\n" ++ "=" ** 70 ++ "\n");
    try stdout.writeAll("  Sumcheck for Constraint Verification\n");
    try stdout.writeAll("=" ** 70 ++ "\n\n");

    const F = field_presets.F17;
    const Multilinear = multilinear.Multilinear(F);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = verifier_module.SumcheckVerifier(F);

    // Scenario: Prove that 4 addition operations were computed correctly
    try stdout.writeAll("🎯 Scenario: Proving Addition Constraints\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("We executed 4 addition operations:\n");

    const operations = [_]struct { a: u64, b: u64, result: u64 }{
        .{ .a = 2, .b = 3, .result = 5 },
        .{ .a = 7, .b = 1, .result = 8 },
        .{ .a = 4, .b = 5, .result = 9 },
        .{ .a = 6, .b = 2, .result = 8 },
    };

    for (operations, 0..) |op, i| {
        try stdout.print("  Step {}: {} + {} = {}\n", .{ i, op.a, op.b, op.result });
    }
    try stdout.writeAll("\n");

    // Build constraint polynomial: C(step) = result - (a + b)
    // If all additions correct, C(step) = 0 for all steps
    // We'll prove: Σ C²(step) = 0 (sum of squared errors)

    try stdout.writeAll("📐 Constraint Polynomial\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("Define: C(step) = result - (a + b)\n");
    try stdout.writeAll("If correct: C(step) = 0 for all steps\n");
    try stdout.writeAll("Prove: Σ C²(step) = 0 over all steps\n\n");

    // Encode as multilinear polynomial
    // For 4 steps, we need 2 variables (2^2 = 4)
    const constraint_evals = [_]F{
        // C²(step_0) = (5 - (2+3))² = 0² = 0
        F.init(0),
        // C²(step_1) = (8 - (7+1))² = 0² = 0
        F.init(0),
        // C²(step_2) = (9 - (4+5))² = 0² = 0
        F.init(0),
        // C²(step_3) = (8 - (6+2))² = 0² = 0
        F.init(0),
    };

    try stdout.writeAll("Constraint evaluations:\n");
    for (constraint_evals, 0..) |eval, i| {
        try stdout.print("  C²(step_{}) = {}\n", .{ i, eval });
    }
    try stdout.writeAll("\n");

    var constraint_poly = try Multilinear.init(allocator, &constraint_evals);
    defer constraint_poly.deinit();

    const constraint_sum = constraint_poly.sumOverHypercube();
    try stdout.print("Sum of squared constraints: {}\n", .{constraint_sum});

    if (constraint_sum.isZero()) {
        try stdout.writeAll("✓ All constraints satisfied! (sum = 0)\n\n");
    } else {
        try stdout.writeAll("✗ Constraints violated! (sum ≠ 0)\n\n");
    }

    // Generate proof
    try stdout.writeAll("🔐 Generating Sumcheck Proof\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    var proof = try Prover.prove(constraint_poly, allocator);
    defer proof.deinit();

    try stdout.writeAll("✓ Proof generated\n");
    try stdout.print("  Proof size: {} round polynomials\n", .{proof.num_vars});
    try stdout.print("  Final point: ({}, {})\n\n", .{
        proof.final_point[0],
        proof.final_point[1],
    });

    // Verify proof
    try stdout.writeAll("✅ Verifying Proof\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    const oracle_fn = struct {
        fn call(point: []const F) !F {
            const evals = [_]F{ F.init(0), F.init(0), F.init(0), F.init(0) };
            var oracle_poly = try Multilinear.init(std.heap.page_allocator, &evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    }.call;

    const result = try Verifier.verify(proof, constraint_sum, &oracle_fn, allocator);

    if (result.is_valid) {
        try stdout.writeAll("✅ VERIFIED!\n");
        try stdout.writeAll("The prover successfully proved that all additions were correct!\n\n");
    } else {
        try stdout.writeAll("❌ VERIFICATION FAILED!\n\n");
    }

    // Now try with incorrect computation
    try stdout.writeAll("🚨 Testing with Incorrect Computation\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("What if step 2 was computed incorrectly?\n");
    try stdout.writeAll("  Claimed: 4 + 5 = 10 (WRONG! Should be 9)\n\n");

    const wrong_evals = [_]F{
        F.init(0), // step 0 correct
        F.init(0), // step 1 correct
        F.init(1), // step 2 WRONG: C²(2) = (10-(4+5))² = 1² = 1
        F.init(0), // step 3 correct
    };

    var wrong_poly = try Multilinear.init(allocator, &wrong_evals);
    defer wrong_poly.deinit();

    const wrong_sum = wrong_poly.sumOverHypercube();
    try stdout.print("Sum of squared constraints: {} (non-zero!)\n", .{wrong_sum});
    try stdout.writeAll("✗ Constraints violated - computation is incorrect!\n\n");

    // Generate proof for wrong computation
    var wrong_proof = try Prover.prove(wrong_poly, allocator);
    defer wrong_proof.deinit();

    const oracle_fn2 = struct {
        fn call(point: []const F) !F {
            const evals = [_]F{ F.init(0), F.init(0), F.init(1), F.init(0) };
            var oracle_poly = try Multilinear.init(std.heap.page_allocator, &evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    }.call;

    const result2 = try Verifier.verify(wrong_proof, wrong_sum, &oracle_fn2, allocator);

    if (result2.is_valid) {
        try stdout.writeAll("✓ Proof verified - but sum is non-zero!\n");
        try stdout.writeAll("Verifier knows computation was INCORRECT.\n\n");
    }

    // Summary
    try stdout.writeAll("📚 How This Works in zkVMs\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("1. Execution trace: Record all inputs/outputs\n");
    try stdout.writeAll("2. Constraints: Define what 'correct' means\n");
    try stdout.writeAll("   - For ADD: output = input1 + input2\n");
    try stdout.writeAll("   - For MUL: output = input1 * input2\n");
    try stdout.writeAll("   - etc.\n");
    try stdout.writeAll("3. Encode constraints as polynomial\n");
    try stdout.writeAll("4. Use sumcheck to prove: Σ C²(step) = 0\n");
    try stdout.writeAll("5. If sum = 0, all constraints satisfied!\n\n");

    try stdout.writeAll("💡 This is the Foundation of zkVMs!\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("Every instruction (ADD, MUL, LOAD, etc.) has constraints.\n");
    try stdout.writeAll("Sumcheck proves all constraints hold across entire execution.\n");
    try stdout.writeAll("Verifier checks in O(log n) time instead of O(n)!\n\n");
}
