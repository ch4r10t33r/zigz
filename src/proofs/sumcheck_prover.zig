const std = @import("std");
const multilinear = @import("../poly/multilinear.zig");
const protocol = @import("sumcheck_protocol.zig");
const hash = @import("../core/hash.zig");

/// Sumcheck Prover
///
/// Generates a sumcheck proof that Σ p(x) over {0,1}^v equals a claimed sum.
///
/// The prover executes v rounds:
/// - Round i: Send univariate polynomial gᵢ(X) = Σ p(r₁,...,rᵢ₋₁,X,xᵢ₊₁,...,xᵥ)
/// - Receive challenge rᵢ from verifier (via Fiat-Shamir)
/// - Update polynomial: p ← p(r₁,...,rᵢ,•)
///
/// After v rounds, send final evaluation p(r₁,...,rᵥ)

pub fn SumcheckProver(comptime F: type) type {
    return struct {
        const Self = @This();
        const Multilinear = multilinear.Multilinear(F);
        const Proof = protocol.SumcheckProof(F);
        const State = protocol.SumcheckState(F);

        /// Generate a sumcheck proof for a multilinear polynomial
        ///
        /// Given p(x₁, ..., xᵥ), prove that Σ p(x) over {0,1}^v equals claimed_sum
        pub fn prove(
            poly: Multilinear,
            allocator: std.mem.Allocator,
        ) !Proof {
            if (poly.num_vars == 0) {
                return error.NoVariables;
            }

            // Initialize proof structure
            var proof = try Proof.init(allocator, poly.num_vars);
            errdefer proof.deinit();

            // Compute initial claim (sum over hypercube)
            const claimed_sum = poly.sumOverHypercube();

            // Initialize state
            var state = try State.init(allocator, poly.num_vars, claimed_sum);
            defer state.deinit();

            // Current polynomial (will be updated each round)
            var current_poly = try Multilinear.init(allocator, poly.evaluations);
            defer current_poly.deinit();

            // Execute sumcheck rounds
            for (0..poly.num_vars) |round| {
                // Generate round polynomial
                const round_poly_coeffs = try current_poly.roundPolynomial(allocator);
                defer allocator.free(round_poly_coeffs);

                // Store in proof
                for (round_poly_coeffs, 0..) |coeff, i| {
                    proof.round_polynomials[round][i] = coeff;
                }

                // Generate challenge (Fiat-Shamir)
                const challenge = state.generateChallenge(round_poly_coeffs);

                // Evaluate round polynomial at challenge
                const eval_at_challenge = protocol.evalUnivariateCoeffs(
                    F,
                    round_poly_coeffs,
                    challenge,
                );

                // Advance state
                state.advance(challenge, eval_at_challenge);

                // Partial evaluation: fix current variable to challenge
                const new_poly = try current_poly.partialEval(challenge, allocator);
                current_poly.deinit();
                current_poly = new_poly;
            }

            // After v rounds, current_poly should be a constant (0 variables)
            if (current_poly.num_vars != 0) {
                return error.ProtocolError;
            }

            // Store final point and evaluation
            for (state.challenges, 0..) |challenge, i| {
                proof.final_point[i] = challenge;
            }
            proof.final_eval = current_poly.evaluations[0];

            return proof;
        }

        /// Simulate interactive proving (for testing)
        ///
        /// This version allows the verifier to provide challenges explicitly,
        /// rather than using Fiat-Shamir. Useful for testing and debugging.
        pub fn proveInteractive(
            poly: Multilinear,
            challenges: []const F,
            allocator: std.mem.Allocator,
        ) !Proof {
            if (poly.num_vars == 0) {
                return error.NoVariables;
            }
            if (challenges.len != poly.num_vars) {
                return error.WrongNumberOfChallenges;
            }

            // Initialize proof structure
            var proof = try Proof.init(allocator, poly.num_vars);
            errdefer proof.deinit();

            // Current polynomial (will be updated each round)
            var current_poly = try Multilinear.init(allocator, poly.evaluations);
            defer current_poly.deinit();

            // Execute sumcheck rounds with provided challenges
            for (0..poly.num_vars) |round| {
                // Generate round polynomial
                const round_poly_coeffs = try current_poly.roundPolynomial(allocator);
                defer allocator.free(round_poly_coeffs);

                // Store in proof
                for (round_poly_coeffs, 0..) |coeff, i| {
                    proof.round_polynomials[round][i] = coeff;
                }

                // Use provided challenge
                const challenge = challenges[round];

                // Partial evaluation with challenge
                const new_poly = try current_poly.partialEval(challenge, allocator);
                current_poly.deinit();
                current_poly = new_poly;
            }

            // Store final point and evaluation
            for (challenges, 0..) |challenge, i| {
                proof.final_point[i] = challenge;
            }
            proof.final_eval = current_poly.evaluations[0];

            return proof;
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "prover: simple 1-variable proof" {
    const F = field.Field(u64, 17);
    const Prover = SumcheckProver(F);
    const MLE = multilinear.Multilinear(F);

    // p(x) with p(0) = 1, p(1) = 2
    // Sum = 1 + 2 = 3
    const evals = [_]F{ F.init(1), F.init(2) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 1), proof.num_vars);
    try testing.expectEqual(@as(usize, 1), proof.round_polynomials.len);

    // Round polynomial g(X) should satisfy g(0) + g(1) = 3
    const g = proof.round_polynomials[0];
    const sum = g[0].add(g[0].add(g[1]));
    try testing.expect(sum.eql(F.init(3)));
}

test "prover: 2-variable proof" {
    const F = field.Field(u64, 17);
    const Prover = SumcheckProver(F);
    const MLE = multilinear.Multilinear(F);

    // 2-variable polynomial
    // p(0,0)=1, p(1,0)=2, p(0,1)=3, p(1,1)=4
    // Sum = 1+2+3+4 = 10
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 2), proof.num_vars);
    try testing.expectEqual(@as(usize, 2), proof.round_polynomials.len);

    // First round polynomial
    // g₁(X) = Σ_{x₂} p(X, x₂) = p(X,0) + p(X,1)
    // g₁(0) = p(0,0) + p(0,1) = 1 + 3 = 4
    // g₁(1) = p(1,0) + p(1,1) = 2 + 4 = 6
    // So g₁(X) = 4 + 2X
    const g1 = proof.round_polynomials[0];
    try testing.expect(g1[0].eql(F.init(4))); // constant term
    try testing.expect(g1[1].eql(F.init(2))); // linear coefficient

    // Check: g₁(0) + g₁(1) should equal total sum
    const eval_0 = g1[0];
    const eval_1 = g1[0].add(g1[1]);
    const sum = eval_0.add(eval_1);
    try testing.expect(sum.eql(F.init(10)));
}

test "prover: 3-variable proof" {
    const F = field.Field(u64, 17);
    const Prover = SumcheckProver(F);
    const MLE = multilinear.Multilinear(F);

    // 3-variable polynomial with evals = [1,2,3,4,5,6,7,8]
    const evals = [_]F{
        F.init(1), F.init(2), F.init(3), F.init(4),
        F.init(5), F.init(6), F.init(7), F.init(8),
    };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    const expected_sum = poly.sumOverHypercube();

    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 3), proof.num_vars);

    // Each round polynomial should maintain sum property
    const g1 = proof.round_polynomials[0];
    const sum1 = g1[0].add(g1[0].add(g1[1]));
    try testing.expect(sum1.eql(expected_sum));
}

test "prover: interactive mode with fixed challenges" {
    const F = field.Field(u64, 17);
    const Prover = SumcheckProver(F);
    const MLE = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    // Provide explicit challenges
    const challenges = [_]F{ F.init(5), F.init(7) };

    var proof = try Prover.proveInteractive(poly, &challenges, testing.allocator);
    defer proof.deinit();

    // Final point should match provided challenges
    for (challenges, 0..) |challenge, i| {
        try testing.expect(proof.final_point[i].eql(challenge));
    }

    // Final evaluation should be p(5, 7)
    const expected = try poly.eval(&challenges);
    try testing.expect(proof.final_eval.eql(expected));
}

test "prover: zero polynomial" {
    const F = field.Field(u64, 17);
    const Prover = SumcheckProver(F);
    const MLE = multilinear.Multilinear(F);

    var zero_poly = try MLE.zero(testing.allocator, 2);
    defer zero_poly.deinit();

    var proof = try Prover.prove(zero_poly, testing.allocator);
    defer proof.deinit();

    // All round polynomials should be zero
    for (proof.round_polynomials) |poly| {
        for (poly) |coeff| {
            try testing.expect(coeff.isZero());
        }
    }

    // Final evaluation should be zero
    try testing.expect(proof.final_eval.isZero());
}

test "prover: constant polynomial" {
    const F = field.Field(u64, 17);
    const Prover = SumcheckProver(F);
    const MLE = multilinear.Multilinear(F);

    // Constant polynomial (all evaluations = 5)
    var const_poly = try MLE.constant(testing.allocator, 2, F.init(5));
    defer const_poly.deinit();

    // Sum should be 5 * 2^2 = 20 = 3 (mod 17)
    const expected_sum = F.init(5).mul(F.init(4));

    var proof = try Prover.prove(const_poly, testing.allocator);
    defer proof.deinit();

    // First round polynomial should have constant sum property
    const g1 = proof.round_polynomials[0];
    const sum = g1[0].add(g1[0].add(g1[1]));
    try testing.expect(sum.eql(expected_sum));
}
