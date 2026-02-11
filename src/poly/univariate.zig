const std = @import("std");

/// Univariate polynomials over finite fields.
///
/// A univariate polynomial is a polynomial in a single variable x:
///   p(x) = a₀ + a₁x + a₂x² + ... + aₙxⁿ
///
/// This implementation uses dense coefficient representation, where
/// coefficients are stored in an array [a₀, a₁, a₂, ..., aₙ].
///
/// Operations are generic over the field type, enabling use with
/// any field from field_presets (Goldilocks, BabyBear, etc.)

/// Univariate polynomial over a finite field
///
/// Generic over field type F, allowing compile-time specialization
/// for different fields (Goldilocks, BabyBear, etc.)
pub fn Univariate(comptime F: type) type {
    return struct {
        /// Coefficients in increasing degree order: [a₀, a₁, a₂, ..., aₙ]
        /// Invariant: coefficients.len > 0 (even zero polynomial has [0])
        coefficients: []F,
        allocator: std.mem.Allocator,

        const Self = @This();

        /// Initialize a polynomial from coefficients
        /// Coefficients are in increasing degree order: [a₀, a₁, a₂, ..., aₙ]
        pub fn init(allocator: std.mem.Allocator, coeffs: []const F) !Self {
            if (coeffs.len == 0) {
                return error.EmptyCoefficients;
            }

            const coefficients = try allocator.dupe(F, coeffs);
            return Self{
                .coefficients = coefficients,
                .allocator = allocator,
            };
        }

        /// Create a zero polynomial (constant 0)
        pub fn zero(allocator: std.mem.Allocator) !Self {
            const coeffs = try allocator.alloc(F, 1);
            coeffs[0] = F.zero();
            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Create a constant polynomial
        pub fn constant(allocator: std.mem.Allocator, value: F) !Self {
            const coeffs = try allocator.alloc(F, 1);
            coeffs[0] = value;
            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Create the identity polynomial p(x) = x
        pub fn identity(allocator: std.mem.Allocator) !Self {
            const coeffs = try allocator.alloc(F, 2);
            coeffs[0] = F.zero(); // Constant term
            coeffs[1] = F.one(); // x coefficient
            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Free the polynomial
        pub fn deinit(self: *Self) void {
            self.allocator.free(self.coefficients);
        }

        /// Get the degree of the polynomial
        /// Returns the index of the highest non-zero coefficient
        /// Zero polynomial has degree 0 by convention
        pub fn degree(self: Self) usize {
            // Find highest non-zero coefficient
            var deg: usize = 0;
            for (self.coefficients, 0..) |coeff, i| {
                if (!coeff.isZero()) {
                    deg = i;
                }
            }
            return deg;
        }

        /// Check if polynomial is zero
        pub fn isZero(self: Self) bool {
            for (self.coefficients) |coeff| {
                if (!coeff.isZero()) {
                    return false;
                }
            }
            return true;
        }

        /// Check if polynomial is constant
        pub fn isConstant(self: Self) bool {
            return self.degree() == 0;
        }

        /// Evaluate polynomial at a point using Horner's method
        ///
        /// Horner's method: p(x) = a₀ + x(a₁ + x(a₂ + x(...)))
        /// This is more efficient than naive evaluation, requiring only
        /// n multiplications and n additions for degree n polynomial.
        ///
        /// Time complexity: O(n) where n is degree
        pub fn eval(self: Self, x: F) F {
            if (self.coefficients.len == 0) {
                return F.zero();
            }

            // Horner's method: start from highest degree
            var result = self.coefficients[self.coefficients.len - 1];

            // Work backwards through coefficients
            var i = self.coefficients.len - 1;
            while (i > 0) : (i -= 1) {
                result = result.mul(x).add(self.coefficients[i - 1]);
            }

            return result;
        }

        /// Evaluate polynomial at multiple points
        /// Returns array of evaluations
        pub fn evalMany(self: Self, points: []const F, allocator: std.mem.Allocator) ![]F {
            const results = try allocator.alloc(F, points.len);
            for (points, 0..) |point, i| {
                results[i] = self.eval(point);
            }
            return results;
        }

        /// Add two polynomials: (a + b)(x)
        pub fn add(self: Self, other: Self, allocator: std.mem.Allocator) !Self {
            const max_len = @max(self.coefficients.len, other.coefficients.len);
            const coeffs = try allocator.alloc(F, max_len);

            for (0..max_len) |i| {
                const a = if (i < self.coefficients.len) self.coefficients[i] else F.zero();
                const b = if (i < other.coefficients.len) other.coefficients[i] else F.zero();
                coeffs[i] = a.add(b);
            }

            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Subtract two polynomials: (a - b)(x)
        pub fn sub(self: Self, other: Self, allocator: std.mem.Allocator) !Self {
            const max_len = @max(self.coefficients.len, other.coefficients.len);
            const coeffs = try allocator.alloc(F, max_len);

            for (0..max_len) |i| {
                const a = if (i < self.coefficients.len) self.coefficients[i] else F.zero();
                const b = if (i < other.coefficients.len) other.coefficients[i] else F.zero();
                coeffs[i] = a.sub(b);
            }

            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Multiply polynomial by a scalar: c·p(x)
        pub fn scalarMul(self: Self, scalar: F, allocator: std.mem.Allocator) !Self {
            const coeffs = try allocator.alloc(F, self.coefficients.len);

            for (self.coefficients, 0..) |coeff, i| {
                coeffs[i] = coeff.mul(scalar);
            }

            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Negate polynomial: -p(x)
        pub fn neg(self: Self, allocator: std.mem.Allocator) !Self {
            const coeffs = try allocator.alloc(F, self.coefficients.len);

            for (self.coefficients, 0..) |coeff, i| {
                coeffs[i] = coeff.neg();
            }

            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Multiply two polynomials: (a · b)(x)
        ///
        /// Uses naive O(n²) multiplication.
        /// TODO: Implement FFT-based multiplication for large polynomials (O(n log n))
        pub fn mul(self: Self, other: Self, allocator: std.mem.Allocator) !Self {
            if (self.isZero() or other.isZero()) {
                return zero(allocator);
            }

            // Result has degree = deg(a) + deg(b)
            const result_len = self.coefficients.len + other.coefficients.len - 1;
            const coeffs = try allocator.alloc(F, result_len);

            // Initialize to zero
            for (coeffs) |*coeff| {
                coeff.* = F.zero();
            }

            // Convolve coefficients
            for (self.coefficients, 0..) |a_coeff, i| {
                for (other.coefficients, 0..) |b_coeff, j| {
                    coeffs[i + j] = coeffs[i + j].add(a_coeff.mul(b_coeff));
                }
            }

            return Self{
                .coefficients = coeffs,
                .allocator = allocator,
            };
        }

        /// Compose two polynomials: p(q(x))
        ///
        /// Evaluates polynomial p at q(x) where q is another polynomial
        pub fn compose(self: Self, inner: Self, allocator: std.mem.Allocator) !Self {
            if (self.coefficients.len == 0) {
                return zero(allocator);
            }

            // Start with the highest degree coefficient
            var result = try constant(allocator, self.coefficients[self.coefficients.len - 1]);
            defer result.deinit();

            // Horner's method for polynomial composition
            var i = self.coefficients.len - 1;
            while (i > 0) : (i -= 1) {
                // result = result * inner + coeff[i-1]
                const temp = try result.mul(inner, allocator);
                result.deinit();
                result = temp;

                const c = try constant(allocator, self.coefficients[i - 1]);
                defer c.deinit();

                const temp2 = try result.add(c, allocator);
                result.deinit();
                result = temp2;
            }

            return result;
        }

        /// Format for printing
        pub fn format(
            self: Self,
            comptime fmt: []const u8,
            options: std.fmt.FormatOptions,
            writer: anytype,
        ) !void {
            _ = fmt;
            _ = options;

            try writer.writeAll("poly(");
            for (self.coefficients, 0..) |coeff, i| {
                if (i > 0) {
                    try writer.writeAll(" + ");
                }
                try writer.print("{}x^{}", .{ coeff, i });
            }
            try writer.writeAll(")");
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "univariate: initialization" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    const coeffs = [_]F{ F.init(1), F.init(2), F.init(3) }; // 1 + 2x + 3x²
    var p = try Poly.init(testing.allocator, &coeffs);
    defer p.deinit();

    try testing.expectEqual(@as(usize, 3), p.coefficients.len);
    try testing.expect(p.coefficients[0].eql(F.init(1)));
    try testing.expect(p.coefficients[1].eql(F.init(2)));
    try testing.expect(p.coefficients[2].eql(F.init(3)));
}

test "univariate: zero and constant polynomials" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    var zero_poly = try Poly.zero(testing.allocator);
    defer zero_poly.deinit();
    try testing.expect(zero_poly.isZero());

    var const_poly = try Poly.constant(testing.allocator, F.init(5));
    defer const_poly.deinit();
    try testing.expect(const_poly.isConstant());
    try testing.expect(const_poly.coefficients[0].eql(F.init(5)));
}

test "univariate: identity polynomial" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    var id = try Poly.identity(testing.allocator);
    defer id.deinit();

    // p(x) = x, so p(5) = 5
    const result = id.eval(F.init(5));
    try testing.expect(result.eql(F.init(5)));
}

test "univariate: degree" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    const coeffs = [_]F{ F.init(1), F.init(2), F.init(0), F.init(3) }; // 1 + 2x + 3x³
    var p = try Poly.init(testing.allocator, &coeffs);
    defer p.deinit();

    try testing.expectEqual(@as(usize, 3), p.degree());
}

test "univariate: Horner evaluation" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    // p(x) = 1 + 2x + 3x²
    const coeffs = [_]F{ F.init(1), F.init(2), F.init(3) };
    var p = try Poly.init(testing.allocator, &coeffs);
    defer p.deinit();

    // p(2) = 1 + 2*2 + 3*4 = 1 + 4 + 12 = 17 = 0 (mod 17)
    const result = p.eval(F.init(2));
    try testing.expect(result.isZero());

    // p(0) = 1
    const result0 = p.eval(F.zero());
    try testing.expect(result0.eql(F.init(1)));

    // p(1) = 1 + 2 + 3 = 6
    const result1 = p.eval(F.one());
    try testing.expect(result1.eql(F.init(6)));
}

test "univariate: addition" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    // p(x) = 1 + 2x
    const coeffs_p = [_]F{ F.init(1), F.init(2) };
    var p = try Poly.init(testing.allocator, &coeffs_p);
    defer p.deinit();

    // q(x) = 3 + 4x + 5x²
    const coeffs_q = [_]F{ F.init(3), F.init(4), F.init(5) };
    var q = try Poly.init(testing.allocator, &coeffs_q);
    defer q.deinit();

    // r(x) = p(x) + q(x) = 4 + 6x + 5x²
    var r = try p.add(q, testing.allocator);
    defer r.deinit();

    try testing.expect(r.coefficients[0].eql(F.init(4)));
    try testing.expect(r.coefficients[1].eql(F.init(6)));
    try testing.expect(r.coefficients[2].eql(F.init(5)));
}

test "univariate: subtraction" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    // p(x) = 5 + 3x
    const coeffs_p = [_]F{ F.init(5), F.init(3) };
    var p = try Poly.init(testing.allocator, &coeffs_p);
    defer p.deinit();

    // q(x) = 2 + 1x
    const coeffs_q = [_]F{ F.init(2), F.init(1) };
    var q = try Poly.init(testing.allocator, &coeffs_q);
    defer q.deinit();

    // r(x) = p(x) - q(x) = 3 + 2x
    var r = try p.sub(q, testing.allocator);
    defer r.deinit();

    try testing.expect(r.coefficients[0].eql(F.init(3)));
    try testing.expect(r.coefficients[1].eql(F.init(2)));
}

test "univariate: scalar multiplication" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    // p(x) = 1 + 2x + 3x²
    const coeffs = [_]F{ F.init(1), F.init(2), F.init(3) };
    var p = try Poly.init(testing.allocator, &coeffs);
    defer p.deinit();

    // r(x) = 2·p(x) = 2 + 4x + 6x²
    var r = try p.scalarMul(F.init(2), testing.allocator);
    defer r.deinit();

    try testing.expect(r.coefficients[0].eql(F.init(2)));
    try testing.expect(r.coefficients[1].eql(F.init(4)));
    try testing.expect(r.coefficients[2].eql(F.init(6)));
}

test "univariate: multiplication" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    // p(x) = 1 + 2x
    const coeffs_p = [_]F{ F.init(1), F.init(2) };
    var p = try Poly.init(testing.allocator, &coeffs_p);
    defer p.deinit();

    // q(x) = 3 + 4x
    const coeffs_q = [_]F{ F.init(3), F.init(4) };
    var q = try Poly.init(testing.allocator, &coeffs_q);
    defer q.deinit();

    // r(x) = p(x)·q(x) = (1 + 2x)(3 + 4x) = 3 + 10x + 8x²
    var r = try p.mul(q, testing.allocator);
    defer r.deinit();

    try testing.expect(r.coefficients[0].eql(F.init(3))); // 1*3
    try testing.expect(r.coefficients[1].eql(F.init(10))); // 1*4 + 2*3
    try testing.expect(r.coefficients[2].eql(F.init(8))); // 2*4
}

test "univariate: polynomial properties" {
    const F = field.Field(u64, 17);
    const Poly = Univariate(F);

    const coeffs = [_]F{ F.init(1), F.init(2), F.init(3) };
    var p = try Poly.init(testing.allocator, &coeffs);
    defer p.deinit();

    // Test that p(x) - p(x) = 0
    var diff = try p.sub(p, testing.allocator);
    defer diff.deinit();
    try testing.expect(diff.isZero());

    // Test that p(x) + 0 = p(x)
    var zero_poly = try Poly.zero(testing.allocator);
    defer zero_poly.deinit();

    var sum = try p.add(zero_poly, testing.allocator);
    defer sum.deinit();

    // Check all coefficients match
    for (p.coefficients, 0..) |coeff, i| {
        try testing.expect(sum.coefficients[i].eql(coeff));
    }
}
