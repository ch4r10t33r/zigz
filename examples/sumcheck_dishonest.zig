/// Dishonest Prover Example
///
/// This example demonstrates how sumcheck catches a cheating prover.
/// Shows why soundness is important and how the verifier detects fraud.

const std = @import("std");
const zigz = @import("zigz");
const field_presets = zigz.field_presets;
const multilinear = zigz.multilinear;
const prover_module = zigz.prover_module;
const verifier_module = zigz.verifier_module;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const stdout = std.io.getStdOut().writer();

    try stdout.writeAll("\n" ++ "=" ** 70 ++ "\n");
    try stdout.writeAll("  Sumcheck Protocol - Catching Dishonest Provers\n");
    try stdout.writeAll("=" ** 70 ++ "\n\n");

    const F = field_presets.F17;
    const Multilinear = multilinear.Multilinear(F);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = verifier_module.SumcheckVerifier(F);

    // Scenario 1: Wrong claimed sum
    try stdout.writeAll("🚨 Scenario 1: Prover Claims Wrong Sum\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try Multilinear.init(allocator, &evals);
    defer poly.deinit();

    const correct_sum = poly.sumOverHypercube();
    const wrong_sum = correct_sum.add(F.init(5)); // Lie about the sum!

    try stdout.print("Actual sum: {}\n", .{correct_sum});
    try stdout.print("Claimed sum: {} (WRONG!)\n\n", .{wrong_sum});

    var proof = try Prover.prove(poly, allocator);
    defer proof.deinit();

    const oracle_fn1 = struct {
        fn call(point: []const F) !F {
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try Multilinear.init(std.heap.page_allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    }.call;

    const result1 = try Verifier.verify(proof, wrong_sum, &oracle_fn1, allocator);

    if (result1.is_valid) {
        try stdout.writeAll("❌ BUG: Verifier accepted wrong sum!\n\n");
    } else {
        try stdout.writeAll("✅ CAUGHT! Verifier rejected the proof.\n");
        try stdout.writeAll("   The first round polynomial didn't satisfy g(0)+g(1)=claimed_sum\n\n");
    }

    // Scenario 2: Tampered round polynomial
    try stdout.writeAll("🚨 Scenario 2: Prover Tampers With Round Polynomial\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    var proof2 = try Prover.prove(poly, allocator);
    defer proof2.deinit();

    // Tamper with the first round polynomial
    const original = proof2.round_polynomials[0][0];
    proof2.round_polynomials[0][0] = original.add(F.init(1));

    try stdout.print("Original coefficient: {}\n", .{original});
    try stdout.print("Tampered coefficient: {} (modified!)\n\n", .{proof2.round_polynomials[0][0]});

    const oracle_fn2 = struct {
        fn call(point: []const F) !F {
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try Multilinear.init(std.heap.page_allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    }.call;

    const result2 = try Verifier.verify(proof2, correct_sum, &oracle_fn2, allocator);

    if (result2.is_valid) {
        try stdout.writeAll("❌ BUG: Verifier accepted tampered proof!\n\n");
    } else {
        try stdout.writeAll("✅ CAUGHT! Verifier rejected the proof.\n");
        try stdout.writeAll("   The round polynomial check failed!\n\n");
    }

    // Scenario 3: Honest prover for comparison
    try stdout.writeAll("✅ Scenario 3: Honest Prover (Control)\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    var proof3 = try Prover.prove(poly, allocator);
    defer proof3.deinit();

    const oracle_fn3 = struct {
        fn call(point: []const F) !F {
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try Multilinear.init(std.heap.page_allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    }.call;

    const result3 = try Verifier.verify(proof3, correct_sum, &oracle_fn3, allocator);

    if (result3.is_valid) {
        try stdout.writeAll("✅ ACCEPTED! Honest prover's proof is valid.\n\n");
    } else {
        try stdout.writeAll("❌ BUG: Honest prover was rejected!\n\n");
    }

    // Summary
    try stdout.writeAll("📊 Summary\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("✓ Wrong sum → Caught\n");
    try stdout.writeAll("✓ Tampered polynomial → Caught\n");
    try stdout.writeAll("✓ Honest prover → Accepted\n\n");

    try stdout.writeAll("🛡️ Why Sumcheck is Secure:\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("1. Each round checks g(0)+g(1) = current_claim\n");
    try stdout.writeAll("2. Random challenges make it hard to predict verification path\n");
    try stdout.writeAll("3. Final oracle call catches any inconsistency\n");
    try stdout.writeAll("4. Soundness error is ~v/|F| where |F| = field size\n");
    try stdout.writeAll("5. For F17: error ~2/17 ≈ 12% (use larger fields in practice!)\n\n");
}
