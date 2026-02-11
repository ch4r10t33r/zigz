const std = @import("std");

/// Multilinear polynomials over finite fields.
///
/// A multilinear polynomial in v variables is a polynomial where each
/// variable has degree at most 1. For example:
///   p(x₁, x₂, x₃) = a₀ + a₁x₁ + a₂x₂ + a₃x₁x₂ + a₄x₃ + a₅x₁x₃ + a₆x₂x₃ + a₇x₁x₂x₃
///
/// Key properties:
/// - A v-variate multilinear polynomial is uniquely determined by its
///   evaluations on the boolean hypercube {0,1}^v
/// - Number of evaluations = 2^v
/// - Used extensively in sumcheck protocol and zkVM constraint systems
///
/// This implementation uses dense representation: store all 2^v evaluations
/// on the boolean hypercube.

/// Multilinear polynomial over a finite field
///
/// Represents a multilinear polynomial by its evaluations on {0,1}^v
pub fn Multilinear(comptime F: type) type {
    return struct {
        /// Evaluations on boolean hypercube {0,1}^v
        /// Length must be a power of 2: evaluations.len = 2^num_vars
        /// Index i corresponds to binary representation of (x_v-1, ..., x_1, x_0)
        evaluations: []F,

        /// Number of variables
        num_vars: usize,

        allocator: std.mem.Allocator,

        const Self = @This();

        /// Initialize from evaluations on boolean hypercube
        /// evaluations.len must be a power of 2
        pub fn init(allocator: std.mem.Allocator, evals: []const F) !Self {
            if (evals.len == 0) {
                return error.EmptyEvaluations;
            }

            // Check that length is a power of 2
            if (!isPowerOfTwo(evals.len)) {
                return error.LengthNotPowerOfTwo;
            }

            const num_vars = std.math.log2(evals.len);
            const evaluations = try allocator.dupe(F, evals);

            return Self{
                .evaluations = evaluations,
                .num_vars = num_vars,
                .allocator = allocator,
            };
        }

        /// Create zero polynomial (all evaluations are zero)
        pub fn zero(allocator: std.mem.Allocator, num_vars: usize) !Self {
            const len = @as(usize, 1) << @intCast(num_vars);
            const evals = try allocator.alloc(F, len);

            for (evals) |*e| {
                e.* = F.zero();
            }

            return Self{
                .evaluations = evals,
                .num_vars = num_vars,
                .allocator = allocator,
            };
        }

        /// Create constant polynomial (all evaluations are the same)
        pub fn constant(allocator: std.mem.Allocator, num_vars: usize, value: F) !Self {
            const len = @as(usize, 1) << @intCast(num_vars);
            const evals = try allocator.alloc(F, len);

            for (evals) |*e| {
                e.* = value;
            }

            return Self{
                .evaluations = evals,
                .num_vars = num_vars,
                .allocator = allocator,
            };
        }

        /// Free the polynomial
        pub fn deinit(self: *Self) void {
            self.allocator.free(self.evaluations);
        }

        /// Check if polynomial is zero
        pub fn isZero(self: Self) bool {
            for (self.evaluations) |e| {
                if (!e.isZero()) {
                    return false;
                }
            }
            return true;
        }

        /// Evaluate polynomial at a point
        ///
        /// Uses multilinear Lagrange interpolation:
        /// p(r₁, ..., rᵥ) = Σ p(b₁, ..., bᵥ) · ∏ᵢ χᵢ(rᵢ, bᵢ)
        /// where χᵢ(r, b) = r if b=1, (1-r) if b=0
        ///
        /// Time complexity: O(2^v) where v is number of variables
        pub fn eval(self: Self, point: []const F) !F {
            if (point.len != self.num_vars) {
                return error.WrongNumberOfVariables;
            }

            // Precompute Lagrange basis coefficients
            // For each variable i, compute [1-rᵢ, rᵢ]
            const basis = try self.allocator.alloc([2]F, self.num_vars);
            defer self.allocator.free(basis);

            for (point, 0..) |r, i| {
                basis[i][0] = F.one().sub(r); // 1 - r
                basis[i][1] = r; // r
            }

            // Sum over all boolean hypercube points
            var result = F.zero();

            for (self.evaluations, 0..) |eval_at_point, idx| {
                // Compute product of Lagrange basis polynomials for this point
                var term = eval_at_point;

                // Extract binary representation of index
                var index = idx;
                for (0..self.num_vars) |var_idx| {
                    const bit = index & 1;
                    term = term.mul(basis[var_idx][bit]);
                    index >>= 1;
                }

                result = result.add(term);
            }

            return result;
        }

        /// Partial evaluation: fix the first variable to a value
        ///
        /// Given p(x₁, x₂, ..., xᵥ), compute q(x₂, ..., xᵥ) = p(r, x₂, ..., xᵥ)
        ///
        /// This is a key operation in the sumcheck protocol, where variables
        /// are fixed one at a time based on verifier challenges.
        ///
        /// Time complexity: O(2^v)
        pub fn partialEval(self: Self, r: F, allocator: std.mem.Allocator) !Self {
            if (self.num_vars == 0) {
                return error.NoVariablesToFix;
            }

            // New polynomial has one fewer variable
            const new_num_vars = self.num_vars - 1;
            const new_len = @as(usize, 1) << @intCast(new_num_vars);
            const new_evals = try allocator.alloc(F, new_len);

            // For each point in the new hypercube, interpolate from the old one
            // p(r, x₂, ..., xᵥ) = (1-r)·p(0, x₂, ..., xᵥ) + r·p(1, x₂, ..., xᵥ)
            for (0..new_len) |i| {
                const eval_at_0 = self.evaluations[i]; // First bit = 0
                const eval_at_1 = self.evaluations[i + new_len]; // First bit = 1

                // Linear interpolation
                const one_minus_r = F.one().sub(r);
                new_evals[i] = one_minus_r.mul(eval_at_0).add(r.mul(eval_at_1));
            }

            return Self{
                .evaluations = new_evals,
                .num_vars = new_num_vars,
                .allocator = allocator,
            };
        }

        /// Sum over boolean hypercube: Σ p(b₁, ..., bᵥ) for all (b₁, ..., bᵥ) ∈ {0,1}^v
        ///
        /// This is used in the sumcheck protocol to compute the claimed sum.
        /// Simply add up all evaluations.
        ///
        /// Time complexity: O(2^v)
        pub fn sumOverHypercube(self: Self) F {
            var sum = F.zero();
            for (self.evaluations) |e| {
                sum = sum.add(e);
            }
            return sum;
        }

        /// Generate the univariate polynomial for sumcheck round
        ///
        /// Given p(x₁, ..., xᵥ), compute the univariate polynomial:
        /// q(X) = Σ_{x₂,...,xᵥ ∈ {0,1}} p(X, x₂, ..., xᵥ)
        ///
        /// This is used in sumcheck: the prover sends q(X) and the verifier
        /// checks that q(0) + q(1) equals the claimed sum.
        ///
        /// Returns coefficients of univariate polynomial in dense form
        pub fn roundPolynomial(self: Self, allocator: std.mem.Allocator) ![]F {
            if (self.num_vars == 0) {
                return error.NoVariables;
            }

            // The round polynomial is at most degree 1 (since multilinear)
            // q(X) = a₀ + a₁·X
            const coeffs = try allocator.alloc(F, 2);

            // q(0) = sum of evaluations where first variable = 0
            // q(1) = sum of evaluations where first variable = 1
            const half = self.evaluations.len / 2;

            var sum_at_0 = F.zero();
            var sum_at_1 = F.zero();

            for (0..half) |i| {
                sum_at_0 = sum_at_0.add(self.evaluations[i]);
                sum_at_1 = sum_at_1.add(self.evaluations[i + half]);
            }

            // Convert point-value form to coefficient form
            // q(X) = q(0) + X·(q(1) - q(0))
            coeffs[0] = sum_at_0; // Constant term
            coeffs[1] = sum_at_1.sub(sum_at_0); // Linear coefficient

            return coeffs;
        }

        /// Add two multilinear polynomials (must have same number of variables)
        pub fn add(self: Self, other: Self, allocator: std.mem.Allocator) !Self {
            if (self.num_vars != other.num_vars) {
                return error.DifferentNumberOfVariables;
            }

            const evals = try allocator.alloc(F, self.evaluations.len);
            for (self.evaluations, other.evaluations, 0..) |a, b, i| {
                evals[i] = a.add(b);
            }

            return Self{
                .evaluations = evals,
                .num_vars = self.num_vars,
                .allocator = allocator,
            };
        }

        /// Scalar multiplication
        pub fn scalarMul(self: Self, scalar: F, allocator: std.mem.Allocator) !Self {
            const evals = try allocator.alloc(F, self.evaluations.len);
            for (self.evaluations, 0..) |e, i| {
                evals[i] = e.mul(scalar);
            }

            return Self{
                .evaluations = evals,
                .num_vars = self.num_vars,
                .allocator = allocator,
            };
        }

        /// Helper: check if a number is a power of 2
        fn isPowerOfTwo(n: usize) bool {
            return n > 0 and (n & (n - 1)) == 0;
        }

        /// Format for printing (shows a few evaluations)
        pub fn format(
            self: Self,
            comptime fmt: []const u8,
            options: std.fmt.FormatOptions,
            writer: anytype,
        ) !void {
            _ = fmt;
            _ = options;

            try writer.print("MLE({} vars, {} evals: [", .{ self.num_vars, self.evaluations.len });
            const show_count = @min(4, self.evaluations.len);
            for (0..show_count) |i| {
                if (i > 0) try writer.writeAll(", ");
                try writer.print("{}", .{self.evaluations[i]});
            }
            if (self.evaluations.len > show_count) {
                try writer.writeAll(", ...");
            }
            try writer.writeAll("])");
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "multilinear: initialization" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // 2-variable polynomial: 4 evaluations
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    try testing.expectEqual(@as(usize, 2), p.num_vars);
    try testing.expectEqual(@as(usize, 4), p.evaluations.len);
}

test "multilinear: power of two check" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // Should fail: not a power of 2
    const bad_evals = [_]F{ F.init(1), F.init(2), F.init(3) };
    try testing.expectError(error.LengthNotPowerOfTwo, MLE.init(testing.allocator, &bad_evals));
}

test "multilinear: zero polynomial" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    var p = try MLE.zero(testing.allocator, 3); // 3 variables, 8 evaluations
    defer p.deinit();

    try testing.expect(p.isZero());
    try testing.expectEqual(@as(usize, 8), p.evaluations.len);
}

test "multilinear: constant polynomial" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    var p = try MLE.constant(testing.allocator, 2, F.init(5));
    defer p.deinit();

    // All evaluations should be 5
    for (p.evaluations) |e| {
        try testing.expect(e.eql(F.init(5)));
    }
}

test "multilinear: evaluation at boolean points" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // 2-variable polynomial with known evaluations
    const evals = [_]F{
        F.init(1), // p(0,0) = 1
        F.init(2), // p(1,0) = 2
        F.init(3), // p(0,1) = 3
        F.init(4), // p(1,1) = 4
    };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    // Evaluate at boolean points should return stored values
    const point_00 = [_]F{ F.zero(), F.zero() };
    const eval_00 = try p.eval(&point_00);
    try testing.expect(eval_00.eql(F.init(1)));

    const point_10 = [_]F{ F.one(), F.zero() };
    const eval_10 = try p.eval(&point_10);
    try testing.expect(eval_10.eql(F.init(2)));

    const point_01 = [_]F{ F.zero(), F.one() };
    const eval_01 = try p.eval(&point_01);
    try testing.expect(eval_01.eql(F.init(3)));

    const point_11 = [_]F{ F.one(), F.one() };
    const eval_11 = try p.eval(&point_11);
    try testing.expect(eval_11.eql(F.init(4)));
}

test "multilinear: evaluation at arbitrary points" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // 1-variable polynomial: p(x) = x
    // p(0) = 0, p(1) = 1
    const evals = [_]F{ F.init(0), F.init(1) };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    // p(2) should equal 2 (by linear interpolation)
    const point = [_]F{F.init(2)};
    const result = try p.eval(&point);
    try testing.expect(result.eql(F.init(2)));

    // p(5) should equal 5
    const point2 = [_]F{F.init(5)};
    const result2 = try p.eval(&point2);
    try testing.expect(result2.eql(F.init(5)));
}

test "multilinear: partial evaluation" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // 2-variable polynomial
    const evals = [_]F{
        F.init(1), // p(0,0) = 1
        F.init(2), // p(1,0) = 2
        F.init(3), // p(0,1) = 3
        F.init(4), // p(1,1) = 4
    };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    // Fix first variable to 0: should get q(x) where q(0) = 1, q(1) = 3
    var q = try p.partialEval(F.zero(), testing.allocator);
    defer q.deinit();

    try testing.expectEqual(@as(usize, 1), q.num_vars);
    try testing.expect(q.evaluations[0].eql(F.init(1))); // q(0)
    try testing.expect(q.evaluations[1].eql(F.init(3))); // q(1)
}

test "multilinear: sum over hypercube" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // 2-variable polynomial: evals = [1, 2, 3, 4]
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    // Sum should be 1 + 2 + 3 + 4 = 10
    const sum = p.sumOverHypercube();
    try testing.expect(sum.eql(F.init(10)));
}

test "multilinear: round polynomial" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // 2-variable polynomial: evals = [1, 2, 3, 4]
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    const coeffs = try p.roundPolynomial(testing.allocator);
    defer testing.allocator.free(coeffs);

    // Round polynomial q(X) sums over second variable
    // q(0) = p(0,0) + p(0,1) = 1 + 3 = 4
    // q(1) = p(1,0) + p(1,1) = 2 + 4 = 6
    // So q(X) = 4 + 2X

    try testing.expect(coeffs[0].eql(F.init(4))); // Constant term
    try testing.expect(coeffs[1].eql(F.init(2))); // Linear coefficient

    // Verify: q(0) + q(1) should equal total sum
    const sum = coeffs[0].add(coeffs[0].add(coeffs[1]));
    try testing.expect(sum.eql(F.init(10)));
}

test "multilinear: addition" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    const evals_p = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var p = try MLE.init(testing.allocator, &evals_p);
    defer p.deinit();

    const evals_q = [_]F{ F.init(5), F.init(6), F.init(7), F.init(8) };
    var q = try MLE.init(testing.allocator, &evals_q);
    defer q.deinit();

    var r = try p.add(q, testing.allocator);
    defer r.deinit();

    // Check element-wise addition
    for (p.evaluations, q.evaluations, r.evaluations) |pe, qe, re| {
        try testing.expect(re.eql(pe.add(qe)));
    }
}

test "multilinear: scalar multiplication" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    var q = try p.scalarMul(F.init(2), testing.allocator);
    defer q.deinit();

    // Each evaluation should be doubled
    for (p.evaluations, q.evaluations) |pe, qe| {
        try testing.expect(qe.eql(pe.mul(F.init(2))));
    }
}

test "multilinear: sumcheck property" {
    const F = field.Field(u64, 17);
    const MLE = Multilinear(F);

    // Key sumcheck property: sum over hypercube equals q(0) + q(1)
    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var p = try MLE.init(testing.allocator, &evals);
    defer p.deinit();

    const total_sum = p.sumOverHypercube();

    const coeffs = try p.roundPolynomial(testing.allocator);
    defer testing.allocator.free(coeffs);

    // q(0) + q(1) = coeffs[0] + (coeffs[0] + coeffs[1])
    const q_0 = coeffs[0];
    const q_1 = coeffs[0].add(coeffs[1]);
    const round_sum = q_0.add(q_1);

    try testing.expect(total_sum.eql(round_sum));
}
