/// Sumcheck Scalability Example
///
/// Demonstrates how sumcheck scales with polynomial size.
/// Shows the exponential savings: O(v) verifier vs O(2^v) naive checking.

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
    try stdout.writeAll("  Sumcheck Protocol - Scalability Demo\n");
    try stdout.writeAll("=" ** 70 ++ "\n\n");

    const F = field_presets.Goldilocks; // Use real field
    const Multilinear = multilinear.Multilinear(F);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = verifier_module.SumcheckVerifier(F);

    try stdout.writeAll("Testing sumcheck with polynomials of increasing size...\n\n");

    try stdout.writeAll("┌────────┬─────────────┬──────────────┬─────────────┐\n");
    try stdout.writeAll("│ Vars   │ # Points    │ Proof Size   │ Naive Work  │\n");
    try stdout.writeAll("├────────┼─────────────┼──────────────┼─────────────┤\n");

    // Test different sizes
    const test_cases = [_]usize{ 1, 2, 3, 4, 5, 6, 7, 8 };

    for (test_cases) |num_vars| {
        const num_points = @as(usize, 1) << @intCast(num_vars);

        // Create polynomial with sequential evaluations
        const evals = try allocator.alloc(F, num_points);
        defer allocator.free(evals);

        for (evals, 0..) |*eval, i| {
            eval.* = F.init(@intCast(i + 1));
        }

        var poly = try Multilinear.init(allocator, evals);
        defer poly.deinit();

        // Compute claimed sum
        const claimed_sum = poly.sumOverHypercube();

        // Generate proof
        const timer_start = std.time.nanoTimestamp();
        var proof = try Prover.prove(poly, allocator);
        const timer_end = std.time.nanoTimestamp();
        defer proof.deinit();

        const prove_time_us = @divFloor(timer_end - timer_start, 1000);

        // Proof size: v round polynomials (2 coefficients each) + v challenges + 1 eval
        const proof_elements = num_vars * 2 + num_vars + 1;

        // Create oracle closure for this specific polynomial
        const OracleContext = struct {
            evals_copy: []const F,
            num_vars_copy: usize,

            fn eval(self: @This(), point: []const F) !F {
                var oracle_poly = try Multilinear.init(std.heap.page_allocator, self.evals_copy);
                defer oracle_poly.deinit();
                return oracle_poly.eval(point);
            }
        };

        _ = OracleContext{
            .evals_copy = evals,
            .num_vars_copy = num_vars,
        };

        // Verify proof
        const verify_start = std.time.nanoTimestamp();

        _ = struct {
            fn call(point: []const F) !F {
                _ = point;
                return F.init(42); // Placeholder (oracle wrapper; not used by verifyRounds)
            }
        }.call;

        const verify_result = try Verifier.verifyRounds(proof, claimed_sum, allocator);
        const verify_end = std.time.nanoTimestamp();

        const verify_time_us = @divFloor(verify_end - verify_start, 1000);

        // Print results
        try stdout.print("│ {:>6} │ {:>11} │ {:>12} │ {:>11} │\n", .{
            num_vars,
            num_points,
            proof_elements,
            num_points, // Naive would need to check all points
        });

        // Show timing for larger cases
        if (num_vars >= 5) {
            try stdout.print("│        │ Prove: {:>4}µs │ Verify: {:>4}µs │             │\n", .{
                prove_time_us,
                verify_time_us,
            });
        }

        _ = verify_result;
    }

    try stdout.writeAll("└────────┴─────────────┴──────────────┴─────────────┘\n\n");

    // Explanation
    try stdout.writeAll("📊 Analysis\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("Proof Size: O(v) field elements\n");
    try stdout.writeAll("Prover Work: O(2^v) - must compute round polynomials\n");
    try stdout.writeAll("Verifier Work: O(v) - just check v round polynomials!\n\n");

    try stdout.writeAll("💡 Key Insight:\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("For v=8 variables:\n");
    try stdout.writeAll("- Naive: Check 256 points\n");
    try stdout.writeAll("- Sumcheck: Check 8 round polynomials + 1 evaluation\n");
    try stdout.writeAll("- Savings: 256 → 9 checks (~28x reduction!)\n\n");

    try stdout.writeAll("For v=20 variables (typical zkVM):\n");
    try stdout.writeAll("- Naive: Check 1,048,576 points\n");
    try stdout.writeAll("- Sumcheck: Check 20 round polynomials\n");
    try stdout.writeAll("- Savings: ~50,000x reduction!\n\n");

    try stdout.writeAll("🚀 Why This Matters for zkVMs:\n");
    try stdout.writeAll("-" ** 70 ++ "\n");
    try stdout.writeAll("- Execution traces are huge (millions of steps)\n");
    try stdout.writeAll("- Encoding as polynomials with v variables\n");
    try stdout.writeAll("- Sumcheck makes verification logarithmic in trace size\n");
    try stdout.writeAll("- This is how we get succinct proofs!\n\n");
}
