const std = @import("std");

/// Value Decomposition for Small Fields
///
/// When using fields smaller than 64 bits (like BabyBear which is 31 bits),
/// we need to decompose larger values into multiple field elements.
///
/// This is essential for zkVMs targeting 64-bit architectures with 31-bit fields.

/// Decompose a 64-bit value into 31-bit chunks for BabyBear field
///
/// A 64-bit value is split into 3 chunks:
/// - Low 31 bits:    bits [0:30]
/// - Middle 31 bits: bits [31:61]
/// - High 2 bits:    bits [62:63]
///
/// Reconstruction: value = low + (middle << 31) + (high << 62)
pub const Decompose64to31 = struct {
    low: u64,    // bits [0:30]  (31 bits, value < 2^31)
    middle: u64, // bits [31:61] (31 bits, value < 2^31)
    high: u64,   // bits [62:63] (2 bits,  value < 4)

    const MASK_31 = (1 << 31) - 1; // 0x7FFFFFFF

    /// Decompose a 64-bit value into three 31-bit chunks
    pub fn fromU64(value: u64) Decompose64to31 {
        return Decompose64to31{
            .low = value & MASK_31,
            .middle = (value >> 31) & MASK_31,
            .high = (value >> 62) & 0x3, // Only 2 bits
        };
    }

    /// Reconstruct the original 64-bit value
    pub fn toU64(self: Decompose64to31) u64 {
        return self.low | (self.middle << 31) | (self.high << 62);
    }

    /// Verify decomposition is valid (for testing)
    pub fn isValid(self: Decompose64to31) bool {
        return self.low < (1 << 31) and
            self.middle < (1 << 31) and
            self.high < 4;
    }

    /// Convert to field elements
    pub fn toFieldElements(self: Decompose64to31, comptime F: type) [3]F {
        return [3]F{
            F.init(self.low),
            F.init(self.middle),
            F.init(self.high),
        };
    }

    /// Create from field elements (for reconstruction in constraints)
    pub fn fromFieldElements(comptime F: type, elements: [3]F) Decompose64to31 {
        return Decompose64to31{
            .low = elements[0].toInt(),
            .middle = elements[1].toInt(),
            .high = elements[2].toInt(),
        };
    }
};

/// Decompose a 64-bit signed value (i64) into 31-bit chunks
///
/// For signed values, we need to handle the sign bit carefully:
/// - Positive values: same as unsigned
/// - Negative values: use two's complement representation
pub const DecomposeI64to31 = struct {
    decomp: Decompose64to31,

    pub fn fromI64(value: i64) DecomposeI64to31 {
        const unsigned: u64 = @bitCast(value);
        return DecomposeI64to31{
            .decomp = Decompose64to31.fromU64(unsigned),
        };
    }

    pub fn toI64(self: DecomposeI64to31) i64 {
        const unsigned = self.decomp.toU64();
        return @bitCast(unsigned);
    }

    pub fn toFieldElements(self: DecomposeI64to31, comptime F: type) [3]F {
        return self.decomp.toFieldElements(F);
    }
};

/// Decompose for BabyBear-specific optimizations
///
/// BabyBear prime: p = 2^31 - 2^27 + 1 = 2,013,265,921
/// This means values < p fit in a single field element
/// But 64-bit values need decomposition
pub const BabyBearDecomp = struct {
    /// Check if a 64-bit value fits in a single BabyBear element
    pub fn fitsInSingle(value: u64) bool {
        const BABYBEAR_PRIME: u64 = 2013265921;
        return value < BABYBEAR_PRIME;
    }

    /// Decompose a 64-bit value for BabyBear field
    /// Returns number of chunks needed (1 or 3)
    pub fn decompose(value: u64) union(enum) {
        Single: u64,
        Triple: Decompose64to31,
    } {
        if (fitsInSingle(value)) {
            return .{ .Single = value };
        } else {
            return .{ .Triple = Decompose64to31.fromU64(value) };
        }
    }
};

// ============================================================================
// Range Constraints
// ============================================================================

/// Generate range constraint witness for a 64-bit value
///
/// Proves that value is in [0, 2^64) by showing each chunk is in valid range:
/// - low in [0, 2^31)
/// - middle in [0, 2^31)
/// - high in [0, 4)
pub fn rangeConstraintWitness(value: u64) Decompose64to31 {
    return Decompose64to31.fromU64(value);
}

/// Verify range constraint: check that reconstruction equals original
pub fn verifyRangeConstraint(decomp: Decompose64to31, original: u64) bool {
    return decomp.toU64() == original and decomp.isValid();
}

// ============================================================================
// Arithmetic with Decomposed Values
// ============================================================================

/// Add two decomposed 64-bit values
///
/// This shows how to perform arithmetic on decomposed values.
/// In the constraint system, we would verify:
/// 1. Decomposition is valid (range constraints)
/// 2. Addition is correct modulo 2^64
pub fn addDecomposed(a: Decompose64to31, b: Decompose64to31) struct {
    sum: Decompose64to31,
    overflow: bool,
} {
    const a_val = a.toU64();
    const b_val = b.toU64();
    const sum_result = @addWithOverflow(a_val, b_val);

    return .{
        .sum = Decompose64to31.fromU64(sum_result[0]),
        .overflow = sum_result[1] == 1,
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const BabyBear = @import("field_presets.zig").BabyBear;

test "decomposition: basic 64-bit to 31-bit" {
    const value: u64 = 0x123456789ABCDEF0;
    const decomp = Decompose64to31.fromU64(value);

    // Verify decomposition is valid
    try testing.expect(decomp.isValid());

    // Verify reconstruction
    try testing.expectEqual(value, decomp.toU64());

    // Check individual chunks
    try testing.expectEqual(@as(u64, 0x1ABCDEF0), decomp.low);
    try testing.expectEqual(@as(u64, 0x2468ACF1), decomp.middle);
    try testing.expectEqual(@as(u64, 0), decomp.high);
}

test "decomposition: max 64-bit value" {
    const max_val: u64 = 0xFFFFFFFFFFFFFFFF;
    const decomp = Decompose64to31.fromU64(max_val);

    try testing.expect(decomp.isValid());
    try testing.expectEqual(max_val, decomp.toU64());

    // Check that high bits are extracted correctly
    try testing.expectEqual(@as(u64, 0x7FFFFFFF), decomp.low);
    try testing.expectEqual(@as(u64, 0x7FFFFFFF), decomp.middle);
    try testing.expectEqual(@as(u64, 3), decomp.high); // bits 62-63 are both set
}

test "decomposition: small value" {
    const small: u64 = 42;
    const decomp = Decompose64to31.fromU64(small);

    try testing.expect(decomp.isValid());
    try testing.expectEqual(small, decomp.toU64());

    // Small value should be in low chunk only
    try testing.expectEqual(@as(u64, 42), decomp.low);
    try testing.expectEqual(@as(u64, 0), decomp.middle);
    try testing.expectEqual(@as(u64, 0), decomp.high);
}

test "decomposition: signed value" {
    const negative: i64 = -12345;
    const decomp = DecomposeI64to31.fromI64(negative);

    // Verify reconstruction
    try testing.expectEqual(negative, decomp.toI64());

    // Verify round-trip
    const reconstructed = decomp.toI64();
    try testing.expectEqual(negative, reconstructed);
}

test "decomposition: to field elements" {
    const value: u64 = 0x123456789ABCDEF0;
    const decomp = Decompose64to31.fromU64(value);

    const field_elems = decomp.toFieldElements(BabyBear);

    // Each field element should be valid
    try testing.expect(field_elems[0].value < BabyBear.MODULUS);
    try testing.expect(field_elems[1].value < BabyBear.MODULUS);
    try testing.expect(field_elems[2].value < BabyBear.MODULUS);

    // Reconstruct from field elements
    const reconstructed = Decompose64to31.fromFieldElements(BabyBear, field_elems);
    try testing.expectEqual(value, reconstructed.toU64());
}

test "decomposition: BabyBear single vs triple" {
    // Small value fits in single field element
    const small: u64 = 1000000;
    try testing.expect(BabyBearDecomp.fitsInSingle(small));

    // Large value needs decomposition
    const large: u64 = 0xFFFFFFFF00000000;
    try testing.expect(!BabyBearDecomp.fitsInSingle(large));

    const decomp_result = BabyBearDecomp.decompose(large);
    switch (decomp_result) {
        .Single => unreachable,
        .Triple => |triple| {
            try testing.expectEqual(large, triple.toU64());
        },
    }
}

test "decomposition: range constraint verification" {
    const value: u64 = 0x123456789ABCDEF0;
    const witness = rangeConstraintWitness(value);

    // Verify the constraint
    try testing.expect(verifyRangeConstraint(witness, value));

    // Invalid decomposition should fail
    const invalid = Decompose64to31{
        .low = 0,
        .middle = 0,
        .high = 0,
    };
    try testing.expect(!verifyRangeConstraint(invalid, value));
}

test "decomposition: addition with decomposed values" {
    const a: u64 = 0x1000000000000000;
    const b: u64 = 0x2000000000000000;

    const a_decomp = Decompose64to31.fromU64(a);
    const b_decomp = Decompose64to31.fromU64(b);

    const result = addDecomposed(a_decomp, b_decomp);

    // Verify sum is correct
    try testing.expectEqual(a +% b, result.sum.toU64());
    try testing.expect(!result.overflow);

    // Test overflow case
    const max1: u64 = 0xFFFFFFFFFFFFFFFF;
    const max2: u64 = 1;
    const max1_decomp = Decompose64to31.fromU64(max1);
    const max2_decomp = Decompose64to31.fromU64(max2);

    const overflow_result = addDecomposed(max1_decomp, max2_decomp);
    try testing.expect(overflow_result.overflow);
    try testing.expectEqual(@as(u64, 0), overflow_result.sum.toU64());
}
