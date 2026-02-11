const std = @import("std");
const univariate = @import("univariate.zig");

/// Lagrange basis polynomials and interpolation.
///
/// Lagrange interpolation is a method to construct a polynomial that passes
/// through a given set of points. For points (x₀, y₀), ..., (xₙ, yₙ), the
/// interpolating polynomial is:
///
///   p(x) = Σᵢ yᵢ · Lᵢ(x)
///
/// where Lᵢ(x) is the i-th Lagrange basis polynomial:
///
///   Lᵢ(x) = ∏_{j≠i} (x - xⱼ)/(xᵢ - xⱼ)
///
/// Key properties:
/// - Lᵢ(xᵢ) = 1
/// - Lᵢ(xⱼ) = 0 for j ≠ i
/// - deg(Lᵢ) = n-1 for n points
///
/// Used in:
/// - Polynomial commitments
/// - Reed-Solomon codes
/// - FRI protocol
/// - zkVM constraint checking

/// Lagrange interpolation over a finite field
pub fn LagrangeInterpolation(comptime F: type) type {
    return struct {
        const Self = @This();
        const Univariate = univariate.Univariate(F);

        /// Interpolate a polynomial from point-value pairs
        ///
        /// Given points (x₀, y₀), ..., (xₙ₋₁, yₙ₋₁), compute the unique
        /// polynomial p(x) of degree < n such that p(xᵢ) = yᵢ
        ///
        /// Time complexity: O(n²) where n is number of points
        pub fn interpolate(
            points: []const F,
            values: []const F,
            allocator: std.mem.Allocator,
        ) !Univariate {
            if (points.len != values.len) {
                return error.MismatchedLengths;
            }
            if (points.len == 0) {
                return error.NoPoints;
            }

            // Check for duplicate points
            for (points, 0..) |xi, i| {
                for (points[i + 1 ..]) |xj| {
                    if (xi.eql(xj)) {
                        return error.DuplicatePoints;
                    }
                }
            }

            // Start with zero polynomial
            var result = try Univariate.zero(allocator);
            errdefer result.deinit();

            // Add each Lagrange basis term
            for (0..points.len) |i| {
                // Compute Lᵢ(x)
                var basis = try lagrangeBasis(points, i, allocator);
                defer basis.deinit();

                // Multiply by yᵢ
                var term = try basis.scalarMul(values[i], allocator);
                defer term.deinit();

                // Add to result
                const new_result = try result.add(term, allocator);
                result.deinit();
                result = new_result;
            }

            return result;
        }

        /// Compute the i-th Lagrange basis polynomial
        ///
        /// Lᵢ(x) = ∏_{j≠i} (x - xⱼ)/(xᵢ - xⱼ)
        ///
        /// Properties:
        /// - Lᵢ(xᵢ) = 1
        /// - Lᵢ(xⱼ) = 0 for j ≠ i
        pub fn lagrangeBasis(
            points: []const F,
            i: usize,
            allocator: std.mem.Allocator,
        ) !Univariate {
            if (i >= points.len) {
                return error.IndexOutOfBounds;
            }

            const xi = points[i];

            // Start with constant 1
            var result = try Univariate.constant(allocator, F.one());
            errdefer result.deinit();

            // Multiply by (x - xⱼ)/(xᵢ - xⱼ) for all j ≠ i
            for (points, 0..) |xj, j| {
                if (i == j) continue;

                // Compute denominator: (xᵢ - xⱼ)
                const denom = xi.sub(xj);
                if (denom.isZero()) {
                    return error.DuplicatePoints;
                }

                const denom_inv = try denom.inv();

                // (x - xⱼ) as polynomial
                const linear = [_]F{ xj.neg(), F.one() }; // -xⱼ + x
                var linear_poly = try Univariate.init(allocator, &linear);
                defer linear_poly.deinit();

                // Scale by 1/(xᵢ - xⱼ)
                var scaled = try linear_poly.scalarMul(denom_inv, allocator);
                defer scaled.deinit();

                // Multiply into result
                const new_result = try result.mul(scaled, allocator);
                result.deinit();
                result = new_result;
            }

            return result;
        }

        /// Evaluate Lagrange basis polynomial at a point
        ///
        /// More efficient than computing the full polynomial when you just
        /// need the value at one point.
        pub fn evalLagrangeBasis(
            points: []const F,
            i: usize,
            x: F,
        ) !F {
            if (i >= points.len) {
                return error.IndexOutOfBounds;
            }

            const xi = points[i];
            var result = F.one();

            for (points, 0..) |xj, j| {
                if (i == j) continue;

                // Compute (x - xⱼ)/(xᵢ - xⱼ)
                const numerator = x.sub(xj);
                const denominator = xi.sub(xj);

                if (denominator.isZero()) {
                    return error.DuplicatePoints;
                }

                const denom_inv = try denominator.inv();
                result = result.mul(numerator.mul(denom_inv));
            }

            return result;
        }

        /// Vanishing polynomial for a set of points
        ///
        /// Z(x) = ∏ᵢ (x - xᵢ)
        ///
        /// This polynomial vanishes (equals zero) at all given points.
        /// Used in:
        /// - Zero-check proofs
        /// - Polynomial division
        /// - Constraint systems
        pub fn vanishingPolynomial(
            points: []const F,
            allocator: std.mem.Allocator,
        ) !Univariate {
            if (points.len == 0) {
                return error.NoPoints;
            }

            // Start with (x - x₀)
            const first = [_]F{ points[0].neg(), F.one() };
            var result = try Univariate.init(allocator, &first);
            errdefer result.deinit();

            // Multiply by (x - xᵢ) for each remaining point
            for (points[1..]) |xi| {
                const linear = [_]F{ xi.neg(), F.one() };
                var linear_poly = try Univariate.init(allocator, &linear);
                defer linear_poly.deinit();

                const new_result = try result.mul(linear_poly, allocator);
                result.deinit();
                result = new_result;
            }

            return result;
        }

        /// Barycentric Lagrange interpolation (more efficient for many evaluations)
        ///
        /// Precomputes barycentric weights and uses them for fast evaluation:
        /// p(x) = Σᵢ wᵢ/(x-xᵢ) · yᵢ / Σᵢ wᵢ/(x-xᵢ)
        ///
        /// where wᵢ = 1/∏_{j≠i}(xᵢ - xⱼ)
        pub const BarycentricForm = struct {
            points: []F,
            values: []F,
            weights: []F,
            allocator: std.mem.Allocator,

            /// Precompute barycentric weights
            pub fn init(
                points: []const F,
                values: []const F,
                allocator: std.mem.Allocator,
            ) !BarycentricForm {
                if (points.len != values.len) {
                    return error.MismatchedLengths;
                }

                const pts = try allocator.dupe(F, points);
                errdefer allocator.free(pts);

                const vals = try allocator.dupe(F, values);
                errdefer allocator.free(vals);

                const weights = try allocator.alloc(F, points.len);
                errdefer allocator.free(weights);

                // Compute weights: wᵢ = 1/∏_{j≠i}(xᵢ - xⱼ)
                for (points, 0..) |xi, i| {
                    var weight = F.one();
                    for (points, 0..) |xj, j| {
                        if (i == j) continue;
                        weight = weight.mul(xi.sub(xj));
                    }
                    weights[i] = try weight.inv();
                }

                return BarycentricForm{
                    .points = pts,
                    .values = vals,
                    .weights = weights,
                    .allocator = allocator,
                };
            }

            pub fn deinit(self: *BarycentricForm) void {
                self.allocator.free(self.points);
                self.allocator.free(self.values);
                self.allocator.free(self.weights);
            }

            /// Evaluate the interpolating polynomial at x
            pub fn eval(self: BarycentricForm, x: F) F {
                // Check if x equals any interpolation point
                for (self.points, 0..) |xi, i| {
                    if (x.eql(xi)) {
                        return self.values[i];
                    }
                }

                // Barycentric formula
                var numerator = F.zero();
                var denominator = F.zero();

                for (self.points, self.values, self.weights) |xi, yi, wi| {
                    const diff = x.sub(xi);
                    const term = wi.mul(diff.inv() catch F.zero()); // Handle division by zero
                    numerator = numerator.add(term.mul(yi));
                    denominator = denominator.add(term);
                }

                return numerator.mul(denominator.inv() catch F.zero());
            }
        };
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "lagrange: simple interpolation" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    // Interpolate through (0, 1), (1, 2), (2, 5)
    const points = [_]F{ F.init(0), F.init(1), F.init(2) };
    const values = [_]F{ F.init(1), F.init(2), F.init(5) };

    var p = try Lagrange.interpolate(&points, &values, testing.allocator);
    defer p.deinit();

    // Verify that p passes through all points
    try testing.expect(p.eval(F.init(0)).eql(F.init(1)));
    try testing.expect(p.eval(F.init(1)).eql(F.init(2)));
    try testing.expect(p.eval(F.init(2)).eql(F.init(5)));
}

test "lagrange: basis polynomial properties" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    const points = [_]F{ F.init(0), F.init(1), F.init(2) };

    // L₀(x) should equal 1 at x=0, and 0 at x=1,2
    var l0 = try Lagrange.lagrangeBasis(&points, 0, testing.allocator);
    defer l0.deinit();

    try testing.expect(l0.eval(F.init(0)).isOne());
    try testing.expect(l0.eval(F.init(1)).isZero());
    try testing.expect(l0.eval(F.init(2)).isZero());

    // L₁(x) should equal 1 at x=1, and 0 at x=0,2
    var l1 = try Lagrange.lagrangeBasis(&points, 1, testing.allocator);
    defer l1.deinit();

    try testing.expect(l1.eval(F.init(0)).isZero());
    try testing.expect(l1.eval(F.init(1)).isOne());
    try testing.expect(l1.eval(F.init(2)).isZero());
}

test "lagrange: vanishing polynomial" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    const points = [_]F{ F.init(1), F.init(2), F.init(3) };

    var z = try Lagrange.vanishingPolynomial(&points, testing.allocator);
    defer z.deinit();

    // Should vanish at all points
    try testing.expect(z.eval(F.init(1)).isZero());
    try testing.expect(z.eval(F.init(2)).isZero());
    try testing.expect(z.eval(F.init(3)).isZero());

    // Should not vanish elsewhere
    try testing.expect(!z.eval(F.init(0)).isZero());
    try testing.expect(!z.eval(F.init(4)).isZero());
}

test "lagrange: barycentric form" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    const points = [_]F{ F.init(0), F.init(1), F.init(2) };
    const values = [_]F{ F.init(1), F.init(2), F.init(5) };

    var bary = try Lagrange.BarycentricForm.init(&points, &values, testing.allocator);
    defer bary.deinit();

    // Should match standard interpolation
    try testing.expect(bary.eval(F.init(0)).eql(F.init(1)));
    try testing.expect(bary.eval(F.init(1)).eql(F.init(2)));
    try testing.expect(bary.eval(F.init(2)).eql(F.init(5)));

    // Test at another point
    const eval_at_3 = bary.eval(F.init(3));
    var p = try Lagrange.interpolate(&points, &values, testing.allocator);
    defer p.deinit();
    const expected = p.eval(F.init(3));

    try testing.expect(eval_at_3.eql(expected));
}

test "lagrange: linear polynomial" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    // p(x) = 2x + 3
    // p(0) = 3, p(1) = 5
    const points = [_]F{ F.init(0), F.init(1) };
    const values = [_]F{ F.init(3), F.init(5) };

    var p = try Lagrange.interpolate(&points, &values, testing.allocator);
    defer p.deinit();

    // p(2) = 2*2 + 3 = 7
    try testing.expect(p.eval(F.init(2)).eql(F.init(7)));

    // p(10) = 2*10 + 3 = 23 = 6 (mod 17)
    try testing.expect(p.eval(F.init(10)).eql(F.init(6)));
}

test "lagrange: duplicate points error" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    const points = [_]F{ F.init(1), F.init(1), F.init(2) };
    const values = [_]F{ F.init(1), F.init(2), F.init(3) };

    try testing.expectError(error.DuplicatePoints, Lagrange.interpolate(&points, &values, testing.allocator));
}

test "lagrange: eval basis directly" {
    const F = field.Field(u64, 17);
    const Lagrange = LagrangeInterpolation(F);

    const points = [_]F{ F.init(0), F.init(1), F.init(2) };

    // Evaluate L₁ at x=5 directly (without building polynomial)
    const result = try Lagrange.evalLagrangeBasis(&points, 1, F.init(5));

    // Compare with full polynomial evaluation
    var l1 = try Lagrange.lagrangeBasis(&points, 1, testing.allocator);
    defer l1.deinit();
    const expected = l1.eval(F.init(5));

    try testing.expect(result.eql(expected));
}
