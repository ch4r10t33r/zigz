const std = @import("std");
const multilinear = @import("../poly/multilinear.zig");
const hash = @import("../core/hash.zig");

/// Sumcheck Protocol Implementation
///
/// The sumcheck protocol allows a prover to convince a verifier that a sum
/// over a multilinear polynomial equals a claimed value, using only O(v)
/// communication where v is the number of variables.
///
/// Protocol flow (v rounds):
/// 1. Prover claims: H = Σ_{x ∈ {0,1}^v} p(x)
/// 2. For each round i = 1 to v:
///    - Prover sends univariate polynomial gᵢ(X)
///    - Verifier checks: gᵢ(0) + gᵢ(1) = current_claim
///    - Verifier sends random challenge rᵢ
///    - Update claim: H ← gᵢ(rᵢ)
/// 3. Final check: H = p(r₁, ..., rᵥ) via oracle
///
/// This implementation uses Fiat-Shamir to make the protocol non-interactive.

/// Sumcheck proof structure
///
/// Contains all the information a prover sends to convince a verifier
pub fn SumcheckProof(comptime F: type) type {
    return struct {
        /// Round polynomials (one per variable)
        /// Each polynomial is in coefficient form: [a₀, a₁]
        /// (Multilinear means each round polynomial is degree 1)
        round_polynomials: [][]F,

        /// Final evaluation point (r₁, ..., rᵥ)
        final_point: []F,

        /// Final evaluation value p(r₁, ..., rᵥ)
        final_eval: F,

        /// Number of variables (= number of rounds)
        num_vars: usize,

        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(
            allocator: std.mem.Allocator,
            num_vars: usize,
        ) !Self {
            const round_polys = try allocator.alloc([]F, num_vars);
            errdefer allocator.free(round_polys);

            // Each round polynomial is degree 1 (for multilinear)
            for (round_polys) |*poly| {
                poly.* = try allocator.alloc(F, 2);
            }

            const final_point = try allocator.alloc(F, num_vars);

            return Self{
                .round_polynomials = round_polys,
                .final_point = final_point,
                .final_eval = F.zero(),
                .num_vars = num_vars,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            for (self.round_polynomials) |poly| {
                self.allocator.free(poly);
            }
            self.allocator.free(self.round_polynomials);
            self.allocator.free(self.final_point);
        }

        /// Serialize proof to bytes
        pub fn toBytes(self: Self, allocator: std.mem.Allocator) ![]u8 {
            // Simple serialization: just concatenate all field elements
            // Format: [num_vars][round_poly_0][round_poly_1]...[final_point][final_eval]

            const total_elems = 1 + (self.num_vars * 2) + self.num_vars + 1;
            const bytes = try allocator.alloc(u8, total_elems * @sizeOf(u64));

            var offset: usize = 0;

            // Write num_vars
            std.mem.writeInt(u64, bytes[offset..][0..8], self.num_vars, .little);
            offset += 8;

            // Write round polynomials
            for (self.round_polynomials) |poly| {
                for (poly) |coeff| {
                    std.mem.writeInt(u64, bytes[offset..][0..8], coeff.toInt(), .little);
                    offset += 8;
                }
            }

            // Write final point
            for (self.final_point) |elem| {
                std.mem.writeInt(u64, bytes[offset..][0..8], elem.toInt(), .little);
                offset += 8;
            }

            // Write final eval
            std.mem.writeInt(u64, bytes[offset..][0..8], self.final_eval.toInt(), .little);

            return bytes;
        }
    };
}

/// Evaluate a univariate polynomial in coefficient form
/// poly = [a₀, a₁] represents a₀ + a₁·X
pub fn evalUnivariateCoeffs(comptime F: type, coeffs: []const F, x: F) F {
    if (coeffs.len == 0) return F.zero();

    // Horner's method
    var result = coeffs[coeffs.len - 1];
    var i = coeffs.len - 1;
    while (i > 0) : (i -= 1) {
        result = result.mul(x).add(coeffs[i - 1]);
    }
    return result;
}

/// Sumcheck protocol state (for interactive version)
///
/// Tracks the current round, accumulated challenges, and current claim
pub fn SumcheckState(comptime F: type) type {
    return struct {
        /// Current round number (0-indexed)
        current_round: usize,

        /// Total number of rounds
        num_rounds: usize,

        /// Accumulated challenges from verifier [r₁, r₂, ...]
        challenges: []F,

        /// Current sum claim (updated each round)
        current_claim: F,

        /// Fiat-Shamir transcript
        transcript: hash.FiatShamirTranscript,

        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(
            allocator: std.mem.Allocator,
            num_rounds: usize,
            initial_claim: F,
        ) !Self {
            const challenges = try allocator.alloc(F, num_rounds);

            return Self{
                .current_round = 0,
                .num_rounds = num_rounds,
                .challenges = challenges,
                .current_claim = initial_claim,
                .transcript = hash.FiatShamirTranscript.init(),
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            self.allocator.free(self.challenges);
        }

        /// Check if protocol is complete
        pub fn isComplete(self: Self) bool {
            return self.current_round >= self.num_rounds;
        }

        /// Generate verifier challenge for current round (Fiat-Shamir)
        pub fn generateChallenge(self: *Self, round_poly: []const F) F {
            // Add round polynomial to transcript
            for (round_poly) |coeff| {
                self.transcript.appendFieldElement(F, coeff);
            }

            // Generate challenge from transcript
            return self.transcript.challenge(F);
        }

        /// Advance to next round with challenge
        pub fn advance(self: *Self, challenge: F, new_claim: F) void {
            self.challenges[self.current_round] = challenge;
            self.current_claim = new_claim;
            self.current_round += 1;
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");
const Multilinear = multilinear.Multilinear;

test "sumcheck: proof initialization" {
    const F = field.Field(u64, 17);
    const Proof = SumcheckProof(F);

    var proof = try Proof.init(testing.allocator, 3);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 3), proof.num_vars);
    try testing.expectEqual(@as(usize, 3), proof.round_polynomials.len);

    // Each round polynomial should be degree 1 (2 coefficients)
    for (proof.round_polynomials) |poly| {
        try testing.expectEqual(@as(usize, 2), poly.len);
    }
}

test "sumcheck: univariate evaluation" {
    const F = field.Field(u64, 17);

    // p(X) = 3 + 5X
    const coeffs = [_]F{ F.init(3), F.init(5) };

    // p(0) = 3
    const eval_0 = evalUnivariateCoeffs(F, &coeffs, F.zero());
    try testing.expect(eval_0.eql(F.init(3)));

    // p(1) = 3 + 5 = 8
    const eval_1 = evalUnivariateCoeffs(F, &coeffs, F.one());
    try testing.expect(eval_1.eql(F.init(8)));

    // p(2) = 3 + 10 = 13
    const eval_2 = evalUnivariateCoeffs(F, &coeffs, F.init(2));
    try testing.expect(eval_2.eql(F.init(13)));
}

test "sumcheck: state initialization" {
    const F = field.Field(u64, 17);
    const State = SumcheckState(F);

    var state = try State.init(testing.allocator, 3, F.init(10));
    defer state.deinit();

    try testing.expectEqual(@as(usize, 0), state.current_round);
    try testing.expectEqual(@as(usize, 3), state.num_rounds);
    try testing.expect(state.current_claim.eql(F.init(10)));
    try testing.expect(!state.isComplete());
}

test "sumcheck: state advancement" {
    const F = field.Field(u64, 17);
    const State = SumcheckState(F);

    var state = try State.init(testing.allocator, 3, F.init(10));
    defer state.deinit();

    // Advance through rounds
    state.advance(F.init(5), F.init(7));
    try testing.expectEqual(@as(usize, 1), state.current_round);
    try testing.expect(state.challenges[0].eql(F.init(5)));
    try testing.expect(state.current_claim.eql(F.init(7)));

    state.advance(F.init(3), F.init(4));
    try testing.expectEqual(@as(usize, 2), state.current_round);

    state.advance(F.init(2), F.init(1));
    try testing.expectEqual(@as(usize, 3), state.current_round);
    try testing.expect(state.isComplete());
}

test "sumcheck: proof serialization" {
    const F = field.Field(u64, 17);
    const Proof = SumcheckProof(F);

    var proof = try Proof.init(testing.allocator, 2);
    defer proof.deinit();

    // Set some values
    proof.round_polynomials[0][0] = F.init(1);
    proof.round_polynomials[0][1] = F.init(2);
    proof.round_polynomials[1][0] = F.init(3);
    proof.round_polynomials[1][1] = F.init(4);
    proof.final_point[0] = F.init(5);
    proof.final_point[1] = F.init(6);
    proof.final_eval = F.init(7);

    const bytes = try proof.toBytes(testing.allocator);
    defer testing.allocator.free(bytes);

    // Should have serialized successfully
    try testing.expect(bytes.len > 0);
}

test "sumcheck: challenge generation determinism" {
    const F = field.Field(u64, 17);
    const State = SumcheckState(F);

    var state1 = try State.init(testing.allocator, 2, F.init(10));
    defer state1.deinit();

    var state2 = try State.init(testing.allocator, 2, F.init(10));
    defer state2.deinit();

    // Same round polynomial should generate same challenge
    const round_poly = [_]F{ F.init(3), F.init(5) };

    const challenge1 = state1.generateChallenge(&round_poly);
    const challenge2 = state2.generateChallenge(&round_poly);

    try testing.expect(challenge1.eql(challenge2));
}
