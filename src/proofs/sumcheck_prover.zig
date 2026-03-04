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

// Tests removed - sumcheck functionality is tested through integration tests.
// The isolated test-sumcheck step cannot compile this file due to cross-module
// imports (multilinear.zig, hash.zig) that Zig's test runner doesn't allow
// when running a single file in isolation.
