const std = @import("std");
const builtin = @import("builtin");

/// Generic finite field implementation parameterized by modulus at compile time.
///
/// A finite field (Galois field) is a set with a finite number of elements where
/// addition, subtraction, multiplication, and division (except by zero) are defined
/// and satisfy the field axioms.
///
/// This implementation uses compile-time generics to specialize the field arithmetic
/// for different moduli, enabling optimizations and type safety.
///
/// Example usage:
/// ```zig
/// const GoldilocksField = Field(u64, 0xFFFFFFFF00000001); // 2^64 - 2^32 + 1
/// var a = GoldilocksField.init(5);
/// var b = GoldilocksField.init(3);
/// var c = a.add(b); // c = 8
/// ```
pub fn Field(comptime T: type, comptime modulus: T) type {
    // Compile-time validation
    if (modulus <= 1) {
        @compileError("Field modulus must be greater than 1");
    }

    return struct {
        value: T,

        const Self = @This();

        /// The modulus of this field (compile-time constant)
        pub const MODULUS: T = modulus;

        /// Initialize a field element from a value
        /// The value is automatically reduced modulo the field modulus
        pub fn init(val: T) Self {
            return Self{ .value = @mod(val, MODULUS) };
        }

        /// Create a field element from a raw value (assumed to be already reduced)
        /// Use this when you know the value is already in [0, MODULUS)
        pub fn fromReduced(val: T) Self {
            std.debug.assert(val < MODULUS);
            return Self{ .value = val };
        }

        /// Return the zero element (additive identity)
        pub fn zero() Self {
            return Self{ .value = 0 };
        }

        /// Return the one element (multiplicative identity)
        pub fn one() Self {
            return Self{ .value = 1 };
        }

        /// Check if this element is zero
        pub fn isZero(self: Self) bool {
            return self.value == 0;
        }

        /// Check if this element is one
        pub fn isOne(self: Self) bool {
            return self.value == 1;
        }

        /// Test equality
        pub fn eql(self: Self, other: Self) bool {
            return self.value == other.value;
        }

        /// Field addition: (a + b) mod p
        pub fn add(self: Self, other: Self) Self {
            // Use wrapping add to handle overflow, then reduce
            const sum = @addWithOverflow(self.value, other.value);
            if (sum[1] == 1) {
                // Overflow occurred
                // (a + b) mod p = ((a + b) - p) when a + b >= p
                // Since overflow occurred, we know the result wraps around
                return Self{ .value = @mod(sum[0], MODULUS) };
            } else {
                // No overflow, but still need to reduce if sum >= MODULUS
                if (sum[0] >= MODULUS) {
                    return Self{ .value = sum[0] - MODULUS };
                }
                return Self{ .value = sum[0] };
            }
        }

        /// Field subtraction: (a - b) mod p
        pub fn sub(self: Self, other: Self) Self {
            if (self.value >= other.value) {
                return Self{ .value = self.value - other.value };
            } else {
                // Need to borrow: (a - b) mod p = (a + p - b) mod p
                return Self{ .value = MODULUS - (other.value - self.value) };
            }
        }

        /// Field negation: -a mod p = (p - a) mod p
        pub fn neg(self: Self) Self {
            if (self.value == 0) {
                return Self.zero();
            }
            return Self{ .value = MODULUS - self.value };
        }

        /// Field multiplication: (a * b) mod p
        ///
        /// For larger types (u128, u256), this needs special handling
        /// Currently implements basic modular multiplication
        pub fn mul(self: Self, other: Self) Self {
            // For types that fit in standard Zig integers, we can use widening multiplication
            const result = switch (@typeInfo(T)) {
                .int => |int_info| blk: {
                    if (int_info.bits <= 32) {
                        // Use u64 for intermediate calculation
                        const wide_a: u64 = @intCast(self.value);
                        const wide_b: u64 = @intCast(other.value);
                        const wide_mod: u64 = @intCast(MODULUS);
                        const product = (wide_a * wide_b) % wide_mod;
                        break :blk @as(T, @intCast(product));
                    } else if (int_info.bits <= 64) {
                        // Use u128 for intermediate calculation
                        const wide_a: u128 = @intCast(self.value);
                        const wide_b: u128 = @intCast(other.value);
                        const wide_mod: u128 = @intCast(MODULUS);
                        const product = (wide_a * wide_b) % wide_mod;
                        break :blk @as(T, @intCast(product));
                    } else {
                        // For u128 and larger, we need Barrett or Montgomery reduction
                        // For now, use @mulWithOverflow and modulo
                        // TODO: Implement Montgomery multiplication for u128+
                        const prod = @mulWithOverflow(self.value, other.value);
                        if (prod[1] != 0) {
                            // Overflow occurred - need multi-precision arithmetic
                            // For MVP, panic; will implement proper reduction later
                            @panic("Multiplication overflow for large field types - Montgomery reduction needed");
                        }
                        break :blk @mod(prod[0], MODULUS);
                    }
                },
                else => @compileError("Field type must be an integer"),
            };

            return Self{ .value = result };
        }

        /// Field squaring: a^2 mod p
        /// Optimized version of mul(self, self)
        pub fn square(self: Self) Self {
            return self.mul(self);
        }

        /// Field inversion: a^(-1) mod p using Extended Euclidean Algorithm
        /// Returns error.NoInverse if element is zero (no multiplicative inverse)
        pub fn inv(self: Self) !Self {
            if (self.isZero()) {
                return error.NoInverse;
            }

            // Extended Euclidean Algorithm
            // Find x such that a*x ≡ 1 (mod p)
            var t: i128 = 0;
            var new_t: i128 = 1;
            var r: i128 = @intCast(MODULUS);
            var new_r: i128 = @intCast(self.value);

            while (new_r != 0) {
                const quotient = @divFloor(r, new_r);

                const temp_t = t;
                t = new_t;
                new_t = temp_t - quotient * new_t;

                const temp_r = r;
                r = new_r;
                new_r = temp_r - quotient * new_r;
            }

            if (r > 1) {
                return error.NoInverse; // Should not happen for prime modulus
            }

            // Ensure result is positive
            if (t < 0) {
                t += @intCast(MODULUS);
            }

            return Self{ .value = @intCast(t) };
        }

        /// Field division: a / b = a * b^(-1) mod p
        /// Returns error.DivisionByZero if divisor is zero
        pub fn div(self: Self, other: Self) !Self {
            const inv_other = try other.inv();
            return self.mul(inv_other);
        }

        /// Exponentiation: a^exp mod p using square-and-multiply
        pub fn pow(self: Self, exp: T) Self {
            if (exp == 0) {
                return Self.one();
            }
            if (exp == 1) {
                return self;
            }

            var result = Self.one();
            var base = self;
            var e = exp;

            while (e > 0) {
                if (e & 1 == 1) {
                    result = result.mul(base);
                }
                base = base.square();
                e >>= 1;
            }

            return result;
        }

        /// Convert to integer (returns the canonical representative in [0, p))
        pub fn toInt(self: Self) T {
            return self.value;
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
            try writer.print("{}", .{self.value});
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "Field: basic initialization" {
    const F = Field(u64, 17); // Small prime for testing

    const a = F.init(5);
    try testing.expectEqual(@as(u64, 5), a.value);

    const b = F.init(20); // Should wrap: 20 mod 17 = 3
    try testing.expectEqual(@as(u64, 3), b.value);
}

test "Field: zero and one" {
    const F = Field(u64, 17);

    const z = F.zero();
    try testing.expect(z.isZero());
    try testing.expectEqual(@as(u64, 0), z.value);

    const o = F.one();
    try testing.expect(o.isOne());
    try testing.expectEqual(@as(u64, 1), o.value);
}

test "Field: addition" {
    const F = Field(u64, 17);

    const a = F.init(5);
    const b = F.init(3);
    const c = a.add(b);
    try testing.expectEqual(@as(u64, 8), c.value);

    // Test wrapping: (10 + 10) mod 17 = 3
    const d = F.init(10);
    const e = F.init(10);
    const f = d.add(e);
    try testing.expectEqual(@as(u64, 3), f.value);
}

test "Field: subtraction" {
    const F = Field(u64, 17);

    const a = F.init(10);
    const b = F.init(3);
    const c = a.sub(b);
    try testing.expectEqual(@as(u64, 7), c.value);

    // Test wrapping: (3 - 10) mod 17 = 10
    const d = F.init(3);
    const e = F.init(10);
    const f = d.sub(e);
    try testing.expectEqual(@as(u64, 10), f.value);
}

test "Field: negation" {
    const F = Field(u64, 17);

    const a = F.init(5);
    const neg_a = a.neg();
    try testing.expectEqual(@as(u64, 12), neg_a.value); // -5 mod 17 = 12

    // Test that a + (-a) = 0
    const sum = a.add(neg_a);
    try testing.expect(sum.isZero());
}

test "Field: multiplication" {
    const F = Field(u64, 17);

    const a = F.init(5);
    const b = F.init(3);
    const c = a.mul(b);
    try testing.expectEqual(@as(u64, 15), c.value);

    // Test wrapping: (10 * 10) mod 17 = 15
    const d = F.init(10);
    const e = d.mul(d);
    try testing.expectEqual(@as(u64, 15), e.value);
}

test "Field: inversion" {
    const F = Field(u64, 17);

    const a = F.init(5);
    const inv_a = try a.inv();

    // 5 * inv(5) should equal 1 mod 17
    const product = a.mul(inv_a);
    try testing.expect(product.isOne());

    // Test that zero has no inverse
    const z = F.zero();
    try testing.expectError(error.NoInverse, z.inv());
}

test "Field: division" {
    const F = Field(u64, 17);

    const a = F.init(10);
    const b = F.init(2);
    const c = try a.div(b);

    // Check: c * b should equal a
    const check = c.mul(b);
    try testing.expect(a.eql(check));

    // Test division by zero
    const z = F.zero();
    try testing.expectError(error.DivisionByZero, a.div(z));
}

test "Field: exponentiation" {
    const F = Field(u64, 17);

    const a = F.init(2);

    // 2^0 = 1
    const p0 = a.pow(0);
    try testing.expect(p0.isOne());

    // 2^1 = 2
    const p1 = a.pow(1);
    try testing.expectEqual(@as(u64, 2), p1.value);

    // 2^4 = 16
    const p4 = a.pow(4);
    try testing.expectEqual(@as(u64, 16), p4.value);

    // 2^5 = 32 mod 17 = 15
    const p5 = a.pow(5);
    try testing.expectEqual(@as(u64, 15), p5.value);
}

test "Field: additive identity" {
    const F = Field(u64, 17);

    const a = F.init(7);
    const z = F.zero();

    try testing.expect(a.add(z).eql(a));
    try testing.expect(z.add(a).eql(a));
}

test "Field: multiplicative identity" {
    const F = Field(u64, 17);

    const a = F.init(7);
    const o = F.one();

    try testing.expect(a.mul(o).eql(a));
    try testing.expect(o.mul(a).eql(a));
}

test "Field: commutativity" {
    const F = Field(u64, 17);

    const a = F.init(5);
    const b = F.init(7);

    // Addition is commutative
    try testing.expect(a.add(b).eql(b.add(a)));

    // Multiplication is commutative
    try testing.expect(a.mul(b).eql(b.mul(a)));
}

test "Field: associativity" {
    const F = Field(u64, 17);

    const a = F.init(3);
    const b = F.init(5);
    const c = F.init(7);

    // Addition is associative: (a + b) + c = a + (b + c)
    const add1 = a.add(b).add(c);
    const add2 = a.add(b.add(c));
    try testing.expect(add1.eql(add2));

    // Multiplication is associative: (a * b) * c = a * (b * c)
    const mul1 = a.mul(b).mul(c);
    const mul2 = a.mul(b.mul(c));
    try testing.expect(mul1.eql(mul2));
}

test "Field: distributivity" {
    const F = Field(u64, 17);

    const a = F.init(3);
    const b = F.init(5);
    const c = F.init(7);

    // Multiplication distributes over addition: a * (b + c) = (a * b) + (a * c)
    const lhs = a.mul(b.add(c));
    const rhs = a.mul(b).add(a.mul(c));
    try testing.expect(lhs.eql(rhs));
}

test "Field: Fermat's Little Theorem" {
    const F = Field(u64, 17);

    // For prime p and a != 0: a^(p-1) ≡ 1 (mod p)
    const a = F.init(5);
    const result = a.pow(16); // 17 - 1 = 16
    try testing.expect(result.isOne());
}
