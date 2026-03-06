/// Basic Sumcheck Example
///
/// This example demonstrates a simple sumcheck proof for a 2-variable polynomial.
/// It shows the complete prover-verifier interaction with detailed output.
const std = @import("std");
const zigz = @import("zigz");
const field = zigz.field;
const field_presets = zigz.field_presets;
const multilinear = zigz.multilinear;
const prover_module = zigz.prover_module;
const verifier_module = zigz.verifier_module;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const stdout = std.fs.File.stdout().deprecatedWriter();

    try stdout.writeAll("\n" ++ "=" ** 70 ++ "\n");
    try stdout.writeAll("  Sumcheck Protocol - Basic Example\n");
    try stdout.writeAll("=" ** 70 ++ "\n\n");

    // Use F17 for easy-to-follow arithmetic
    const F = field_presets.F17;
    const Multilinear = multilinear.Multilinear(F);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = verifier_module.SumcheckVerifier(F);

    // Create a 2-variable polynomial
    // p(x₁, x₂) with evaluations:
    // p(0,0) = 1, p(1,0) = 2, p(0,1) = 3, p(1,1) = 4
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };

    try stdout.writeAll("📊 Polynomial Setup\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("2-variable multilinear polynomial with evaluations:\n");
    try stdout.print("  p(0,0) = {f}\n", .{evals[0]});
    try stdout.print("  p(1,0) = {f}\n", .{evals[1]});
    try stdout.print("  p(0,1) = {f}\n", .{evals[2]});
    try stdout.print("  p(1,1) = {f}\n\n", .{evals[3]});

    var poly = try Multilinear.init(allocator, &evals);
    defer poly.deinit();

    // Compute the claimed sum
    const claimed_sum = poly.sumOverHypercube();
    try stdout.writeAll("🎯 Claimed Sum\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.print("Prover claims: Σ p(x) over {{0,1}}² = {f}\n", .{claimed_sum});
    try stdout.print("(Actual: 1 + 2 + 3 + 4 = {f})\n\n", .{claimed_sum});

    // Generate proof
    try stdout.writeAll("🔐 Prover: Generating Proof\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    var proof = try Prover.prove(poly, allocator);
    defer proof.deinit();

    try stdout.print("✓ Generated proof with {d} rounds\n\n", .{proof.num_vars});

    // Show round polynomials
    try stdout.writeAll("📜 Round Polynomials\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    for (proof.round_polynomials, 0..) |round_poly, i| {
        try stdout.print("Round {d}: g{d}(X) = {f} + {f}·X\n", .{
            i + 1,
            i + 1,
            round_poly[0],
            round_poly[1],
        });

        // Verify sum property
        const g_0 = round_poly[0];
        const g_1 = round_poly[0].add(round_poly[1]);
        const sum = g_0.add(g_1);

        try stdout.print("  g(0) = {f}, g(1) = {f}, g(0)+g(1) = {f}\n", .{ g_0, g_1, sum });
    }

    try stdout.print("\nFinal point: ({f}, {f})\n", .{
        proof.final_point[0],
        proof.final_point[1],
    });
    try stdout.print("Final evaluation: p({f}, {f}) = {f}\n\n", .{
        proof.final_point[0],
        proof.final_point[1],
        proof.final_eval,
    });

    // Verify proof
    try stdout.writeAll("✅ Verifier: Checking Proof\n");
    try stdout.writeAll("-" ** 70 ++ "\n");

    // Oracle function: evaluate the original polynomial
    const Oracle = struct {
        original_poly: *Multilinear,

        fn eval(self: @This(), point: []const F) !F {
            return self.original_poly.eval(point);
        }
    };

    _ = Oracle{ .original_poly = &poly };
    const eval_fn = struct {
        fn call(point: []const F) !F {
            // Reconstruct polynomial for oracle evaluation (same evals as poly)
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try Multilinear.init(std.heap.page_allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    }.call;

    const result = try Verifier.verify(proof, claimed_sum, &eval_fn, allocator);

    if (result.is_valid) {
        try stdout.writeAll("✓ PROOF VERIFIED! ✓\n");
        try stdout.writeAll("The prover successfully proved that the sum is correct!\n\n");
    } else {
        try stdout.writeAll("✗ PROOF REJECTED! ✗\n");
        try stdout.print("Expected: {f}, Got: {f}\n\n", .{
            result.expected_eval,
            result.claimed_eval,
        });
    }

    // Show what happened
    try stdout.writeAll("📖 What Just Happened?\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("1. Prover computed sum over all 2² = 4 points: 1+2+3+4 = 10\n");
    try stdout.writeAll("2. Prover generated 2 round polynomials (one per variable)\n");
    try stdout.writeAll("3. Verifier checked g(0)+g(1) = claimed_sum for each round\n");
    try stdout.writeAll("4. Verifier used challenges to 'zoom in' on a random point\n");
    try stdout.writeAll("5. Final check: evaluate p at that random point\n");
    try stdout.writeAll("6. If honest, prover can't cheat (soundness!)\n\n");

    try stdout.writeAll("🎓 Key Insight:\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("Verifier did O(2) work instead of O(4) to check the sum!\n");
    try stdout.writeAll("For v variables: O(v) vs O(2^v) - exponential savings!\n\n");
}
