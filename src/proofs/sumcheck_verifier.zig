const std = @import("std");
const protocol = @import("sumcheck_protocol.zig");
const hash = @import("../core/hash.zig");

/// Sumcheck Verifier
///
/// Verifies a sumcheck proof with O(v) work, where v is the number of variables.
///
/// Verification steps:
/// 1. Check claimed sum H
/// 2. For each round i = 1 to v:
///    - Check: gᵢ(0) + gᵢ(1) = current_claim
///    - Generate challenge rᵢ (Fiat-Shamir)
///    - Update claim: H ← gᵢ(rᵢ)
/// 3. Final check: H = p(r₁, ..., rᵥ) via oracle
///
/// The verifier never needs to see the full polynomial - only the round
/// polynomials and a single evaluation oracle call at the end.

pub fn SumcheckVerifier(comptime F: type) type {
    return struct {
        const Self = @This();
        const Proof = protocol.SumcheckProof(F);
        const State = protocol.SumcheckState(F);

        /// Verification result
        pub const VerificationResult = struct {
            /// Whether proof is valid
            is_valid: bool,

            /// Final evaluation point (r₁, ..., rᵥ)
            final_point: []const F,

            /// Expected evaluation at final point
            expected_eval: F,

            /// Claimed evaluation from proof
            claimed_eval: F,
        };

        /// Verify a sumcheck proof
        ///
        /// Given:
        /// - proof: The sumcheck proof from prover
        /// - claimed_sum: The claimed sum H = Σ p(x)
        /// - oracle: Function to evaluate p at a point (for final check)
        ///
        /// Returns: VerificationResult indicating success/failure
        pub fn verify(
            proof: Proof,
            claimed_sum: F,
            oracle: *const fn ([]const F) anyerror!F,
            allocator: std.mem.Allocator,
        ) !VerificationResult {
            if (proof.num_vars == 0) {
                return error.NoVariables;
            }

            // Initialize state
            var state = try State.init(allocator, proof.num_vars, claimed_sum);
            defer state.deinit();

            // Verify each round
            for (0..proof.num_vars) |round| {
                const round_poly = proof.round_polynomials[round];

                // Check: g(0) + g(1) = current_claim
                const eval_0 = protocol.evalUnivariateCoeffs(F, round_poly, F.zero());
                const eval_1 = protocol.evalUnivariateCoeffs(F, round_poly, F.one());
                const sum = eval_0.add(eval_1);

                if (!sum.eql(state.current_claim)) {
                    // Sum check failed!
                    return VerificationResult{
                        .is_valid = false,
                        .final_point = proof.final_point,
                        .expected_eval = state.current_claim,
                        .claimed_eval = sum,
                    };
                }

                // Generate challenge (Fiat-Shamir)
                const challenge = state.generateChallenge(round_poly);

                // Evaluate round polynomial at challenge
                const eval_at_challenge = protocol.evalUnivariateCoeffs(
                    F,
                    round_poly,
                    challenge,
                );

                // Advance state
                state.advance(challenge, eval_at_challenge);
            }

            // Final check: evaluate p(r₁, ..., rᵥ) via oracle
            const oracle_eval = try oracle(proof.final_point);

            // Check if oracle evaluation matches final claim
            const matches = oracle_eval.eql(state.current_claim) and
                oracle_eval.eql(proof.final_eval);

            return VerificationResult{
                .is_valid = matches,
                .final_point = proof.final_point,
                .expected_eval = state.current_claim,
                .claimed_eval = proof.final_eval,
            };
        }

        /// Verify with interactive challenges (for testing)
        ///
        /// This version checks the proof against provided challenges,
        /// rather than using Fiat-Shamir. Useful for testing.
        pub fn verifyInteractive(
            proof: Proof,
            claimed_sum: F,
            challenges: []const F,
            oracle: *const fn ([]const F) anyerror!F,
        ) !VerificationResult {
            if (proof.num_vars == 0) {
                return error.NoVariables;
            }
            if (challenges.len != proof.num_vars) {
                return error.WrongNumberOfChallenges;
            }

            var current_claim = claimed_sum;

            // Verify each round
            for (0..proof.num_vars) |round| {
                const round_poly = proof.round_polynomials[round];

                // Check: g(0) + g(1) = current_claim
                const eval_0 = protocol.evalUnivariateCoeffs(F, round_poly, F.zero());
                const eval_1 = protocol.evalUnivariateCoeffs(F, round_poly, F.one());
                const sum = eval_0.add(eval_1);

                if (!sum.eql(current_claim)) {
                    return VerificationResult{
                        .is_valid = false,
                        .final_point = proof.final_point,
                        .expected_eval = current_claim,
                        .claimed_eval = sum,
                    };
                }

                // Use provided challenge
                const challenge = challenges[round];

                // Update claim
                current_claim = protocol.evalUnivariateCoeffs(F, round_poly, challenge);
            }

            // Final check via oracle
            const oracle_eval = try oracle(proof.final_point);

            const matches = oracle_eval.eql(current_claim) and
                oracle_eval.eql(proof.final_eval);

            return VerificationResult{
                .is_valid = matches,
                .final_point = proof.final_point,
                .expected_eval = current_claim,
                .claimed_eval = proof.final_eval,
            };
        }

        /// Fast verification without oracle (assumes oracle check done separately)
        ///
        /// This is useful when you want to batch oracle checks or defer them.
        /// Only checks the round polynomial consistency, not the final evaluation.
        pub fn verifyRounds(
            proof: Proof,
            claimed_sum: F,
            allocator: std.mem.Allocator,
        ) !struct { is_valid: bool, final_claim: F } {
            var state = try State.init(allocator, proof.num_vars, claimed_sum);
            defer state.deinit();

            for (0..proof.num_vars) |round| {
                const round_poly = proof.round_polynomials[round];

                const eval_0 = protocol.evalUnivariateCoeffs(F, round_poly, F.zero());
                const eval_1 = protocol.evalUnivariateCoeffs(F, round_poly, F.one());
                const sum = eval_0.add(eval_1);

                if (!sum.eql(state.current_claim)) {
                    return .{ .is_valid = false, .final_claim = F.zero() };
                }

                const challenge = state.generateChallenge(round_poly);
                const eval_at_challenge = protocol.evalUnivariateCoeffs(
                    F,
                    round_poly,
                    challenge,
                );

                state.advance(challenge, eval_at_challenge);
            }

            return .{
                .is_valid = true,
                .final_claim = state.current_claim,
            };
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");
const multilinear = @import("../poly/multilinear.zig");
const prover_module = @import("sumcheck_prover.zig");

const Multilinear = multilinear.Multilinear;

test "verifier: honest prover passes" {
    const F = field.Field(u64, 17);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = SumcheckVerifier(F);
    const MLE = Multilinear(F);

    // Create a polynomial
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    const claimed_sum = poly.sumOverHypercube();

    // Prover generates proof
    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    // Oracle function: evaluate the original polynomial
    const Oracle = struct {
        fn eval(point: []const F) !F {
            // Re-create polynomial for oracle (in real system, this would be provided)
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try MLE.init(testing.allocator, &oracle_evals);
            defer oracle_poly.deinit();

            return oracle_poly.eval(point);
        }
    };

    // Verifier checks proof
    const result = try Verifier.verify(
        proof,
        claimed_sum,
        &Oracle.eval,
        testing.allocator,
    );

    try testing.expect(result.is_valid);
}

test "verifier: dishonest prover fails (wrong sum)" {
    const F = field.Field(u64, 17);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = SumcheckVerifier(F);
    const MLE = Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    const correct_sum = poly.sumOverHypercube();
    const wrong_sum = correct_sum.add(F.one()); // Off by 1

    // Prover generates proof for correct sum
    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    const Oracle = struct {
        fn eval(point: []const F) !F {
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try MLE.init(testing.allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    };

    // Verifier checks with wrong claimed sum
    const result = try Verifier.verify(
        proof,
        wrong_sum,
        &Oracle.eval,
        testing.allocator,
    );

    // Should fail because claimed sum doesn't match
    try testing.expect(!result.is_valid);
}

test "verifier: tampered round polynomial fails" {
    const F = field.Field(u64, 17);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = SumcheckVerifier(F);
    const MLE = Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    const claimed_sum = poly.sumOverHypercube();

    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    // Tamper with the first round polynomial
    proof.round_polynomials[0][0] = proof.round_polynomials[0][0].add(F.one());

    const Oracle = struct {
        fn eval(point: []const F) !F {
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try MLE.init(testing.allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    };

    const result = try Verifier.verify(
        proof,
        claimed_sum,
        &Oracle.eval,
        testing.allocator,
    );

    // Should fail because round polynomial was tampered with
    try testing.expect(!result.is_valid);
}

test "verifier: interactive mode" {
    const F = field.Field(u64, 17);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = SumcheckVerifier(F);
    const MLE = Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    const claimed_sum = poly.sumOverHypercube();

    // Fixed challenges
    const challenges = [_]F{ F.init(5), F.init(7) };

    // Prover uses same challenges
    var proof = try Prover.proveInteractive(poly, &challenges, testing.allocator);
    defer proof.deinit();

    const Oracle = struct {
        fn eval(point: []const F) !F {
            const oracle_evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
            var oracle_poly = try MLE.init(testing.allocator, &oracle_evals);
            defer oracle_poly.deinit();
            return oracle_poly.eval(point);
        }
    };

    // Verifier uses same challenges
    const result = try Verifier.verifyInteractive(
        proof,
        claimed_sum,
        &challenges,
        &Oracle.eval,
    );

    try testing.expect(result.is_valid);
}

test "verifier: rounds-only verification" {
    const F = field.Field(u64, 17);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = SumcheckVerifier(F);
    const MLE = Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try MLE.init(testing.allocator, &evals);
    defer poly.deinit();

    const claimed_sum = poly.sumOverHypercube();

    var proof = try Prover.prove(poly, testing.allocator);
    defer proof.deinit();

    // Verify only the rounds (not the final oracle check)
    const result = try Verifier.verifyRounds(proof, claimed_sum, testing.allocator);

    try testing.expect(result.is_valid);

    // The final claim should match what oracle would give
    const expected_eval = try poly.eval(proof.final_point);
    try testing.expect(result.final_claim.eql(expected_eval));
}

test "verifier: zero polynomial" {
    const F = field.Field(u64, 17);
    const Prover = prover_module.SumcheckProver(F);
    const Verifier = SumcheckVerifier(F);
    const MLE = Multilinear(F);

    var zero_poly = try MLE.zero(testing.allocator, 2);
    defer zero_poly.deinit();

    var proof = try Prover.prove(zero_poly, testing.allocator);
    defer proof.deinit();

    const Oracle = struct {
        fn eval(point: []const F) !F {
            _ = point;
            return F.zero();
        }
    };

    const result = try Verifier.verify(
        proof,
        F.zero(),
        &Oracle.eval,
        testing.allocator,
    );

    try testing.expect(result.is_valid);
}
