const field = @import("field.zig");
const std = @import("std");

/// Common finite field configurations used in zero-knowledge proofs and cryptography.
///
/// These presets provide convenient access to well-studied fields with efficient
/// arithmetic and good cryptographic properties.

// ============================================================================
// Small Fields (for testing and simple examples)
// ============================================================================

/// Very small prime field for testing (17 elements)
/// Useful for unit tests and understanding field operations
pub const F17 = field.Field(u64, 17);

/// Baby Bear field: p = 2^31 - 2^27 + 1 = 2013265921
/// Used in some STARK systems for 32-bit efficient arithmetic
pub const BabyBear = field.Field(u64, 2013265921);

/// Koala Bear field: p = 2^31 - 2^24 + 1 = 2130706433
/// Another STARK-friendly field with efficient 31-bit arithmetic
/// Used in Plonky3 and some zkVM implementations
pub const KoalaBear = field.Field(u64, 2130706433);

// ============================================================================
// Goldilocks Field (Most Common for STARKs)
// ============================================================================

/// Goldilocks prime: p = 2^64 - 2^32 + 1
///
/// This is one of the most popular fields for STARK-based zkVMs because:
/// - It's the largest prime that fits in 64 bits
/// - Allows efficient 32-bit chunking for lookups
/// - Modular reduction is very efficient
/// - Has a large multiplicative subgroup (2^32 order)
/// - Supports efficient FFTs for polynomial commitments
///
/// The name "Goldilocks" comes from it being "just right" - large enough
/// for security but small enough for efficient 64-bit arithmetic.
pub const Goldilocks = field.Field(u64, 0xFFFFFFFF00000001);

// ============================================================================
// BN254 Scalar Field (for SNARKs and Pairings)
// ============================================================================

/// BN254 scalar field modulus (also called BN128 or alt_bn128)
///
/// This is the scalar field of the BN254 elliptic curve, widely used in:
/// - Ethereum's precompiled contracts
/// - Groth16 SNARKs
/// - Many zkSNARK libraries (libsnark, bellman, arkworks)
///
/// The modulus is: 21888242871839275222246405745257275088548364400416034343698204186575808495617
///
/// For Zig, we need 256-bit integer support. For now, we provide the modulus
/// as a compile-time constant but note that operations on u256 need special handling.
///
/// TODO: Implement proper u256 support with Montgomery reduction
pub const BN254_SCALAR_FIELD_MODULUS: u256 = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

// Note: Uncomment when u256 arithmetic is fully implemented
// pub const BN254Scalar = field.Field(u256, BN254_SCALAR_FIELD_MODULUS);

// ============================================================================
// Mersenne-like Fields
// ============================================================================

/// Mersenne prime: 2^31 - 1 = 2147483647
/// Very efficient for arithmetic (modular reduction is just bit operations)
pub const Mersenne31 = field.Field(u64, 2147483647);

/// Mersenne prime: 2^61 - 1 = 2305843009213693951
/// Larger Mersenne prime, still efficient for modular reduction
pub const Mersenne61 = field.Field(u64, 2305843009213693951);

// ============================================================================
// Utility Functions
// ============================================================================

/// Get a human-readable name for a field type
pub fn fieldName(comptime F: type) []const u8 {
    if (F == F17) return "F17 (test field)";
    if (F == BabyBear) return "BabyBear";
    if (F == KoalaBear) return "KoalaBear";
    if (F == Goldilocks) return "Goldilocks";
    if (F == Mersenne31) return "Mersenne31";
    if (F == Mersenne61) return "Mersenne61";
    return "Unknown field";
}

/// Check if a field has efficient modular reduction (Mersenne-like properties)
pub fn hasEfficientReduction(comptime F: type) bool {
    const mod = F.MODULUS;

    // Check if it's a Mersenne prime (2^n - 1)
    // TODO: Implement proper check

    // Check if it's Goldilocks-like (2^n - 2^m + 1)
    if (mod == 0xFFFFFFFF00000001) return true;

    // Check if it's a Mersenne prime
    if (mod == 2147483647 or mod == 2305843009213693951) return true;

    return false;
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "field_presets: F17 basic operations" {
    const a = F17.init(5);
    const b = F17.init(12);
    const c = a.add(b);

    // 5 + 12 = 17 mod 17 = 0
    try testing.expect(c.isZero());
}

test "field_presets: BabyBear properties" {
    // Test that BabyBear has correct modulus: 2^31 - 2^27 + 1
    try testing.expectEqual(@as(u64, 2013265921), BabyBear.MODULUS);

    // Verify the formula
    const computed: u64 = (@as(u64, 1) << 31) - (@as(u64, 1) << 27) + 1;
    try testing.expectEqual(BabyBear.MODULUS, computed);

    // Test basic arithmetic
    const a = BabyBear.init(1000000);
    const b = BabyBear.init(2000000);
    const c = a.add(b);

    try testing.expectEqual(@as(u64, 3000000), c.value);
}

test "field_presets: KoalaBear properties" {
    // Test that KoalaBear has correct modulus: 2^31 - 2^24 + 1
    try testing.expectEqual(@as(u64, 2130706433), KoalaBear.MODULUS);

    // Verify the formula
    const computed: u64 = (@as(u64, 1) << 31) - (@as(u64, 1) << 24) + 1;
    try testing.expectEqual(KoalaBear.MODULUS, computed);

    // Test basic arithmetic
    const a = KoalaBear.init(1000000);
    const b = KoalaBear.init(2000000);
    const c = a.add(b);

    try testing.expectEqual(@as(u64, 3000000), c.value);

    // Test that it's a valid prime field
    const x = KoalaBear.init(12345);
    const x_inv = try x.inv();
    const unity = x.mul(x_inv);
    try testing.expect(unity.isOne());
}

test "field_presets: Goldilocks properties" {
    // Test that Goldilocks has correct modulus: 2^64 - 2^32 + 1
    const expected_mod: u64 = 0xFFFFFFFF00000001;
    try testing.expectEqual(expected_mod, Goldilocks.MODULUS);

    // Test that it's indeed 2^64 - 2^32 + 1
    const computed: u128 = (@as(u128, 1) << 64) - (@as(u128, 1) << 32) + 1;
    try testing.expectEqual(@as(u128, expected_mod), computed);

    // Test basic arithmetic
    const a = Goldilocks.init(12345678901234567);
    const b = Goldilocks.init(98765432109876543);
    const sum = a.add(b);

    // Verify the sum is correct
    const expected = (12345678901234567 + 98765432109876543) % Goldilocks.MODULUS;
    try testing.expectEqual(expected, sum.value);
}

test "field_presets: Goldilocks 32-bit chunking property" {
    // Goldilocks is designed to work well with 32-bit chunks
    // This is important for Lasso lookup table decomposition

    const a = Goldilocks.init(0x123456789ABCDEF0);

    // Split into two 32-bit chunks
    const low: u32 = @truncate(a.value & 0xFFFFFFFF);
    const high: u32 = @truncate((a.value >> 32) & 0xFFFFFFFF);

    // Reconstruct
    const reconstructed: u64 = (@as(u64, high) << 32) | @as(u64, low);

    try testing.expectEqual(a.value, reconstructed);
}

test "field_presets: Mersenne31 efficient reduction" {
    // Mersenne primes have efficient reduction: a mod (2^n - 1)
    // This test verifies basic properties

    try testing.expectEqual(@as(u64, 2147483647), Mersenne31.MODULUS);

    // Mersenne31 is 2^31 - 1, so (2^31 - 1) + 1 should equal 0
    const max = Mersenne31.init(Mersenne31.MODULUS);
    const one = Mersenne31.one();
    const sum = max.add(one);

    try testing.expect(sum.isZero());
}

test "field_presets: fieldName utility" {
    try testing.expectEqualStrings("F17 (test field)", fieldName(F17));
    try testing.expectEqualStrings("BabyBear", fieldName(BabyBear));
    try testing.expectEqualStrings("KoalaBear", fieldName(KoalaBear));
    try testing.expectEqualStrings("Goldilocks", fieldName(Goldilocks));
    try testing.expectEqualStrings("Mersenne31", fieldName(Mersenne31));
    try testing.expectEqualStrings("Mersenne61", fieldName(Mersenne61));
}

test "field_presets: all fields support basic operations" {
    // Compile-time test that all defined fields support the required operations
    inline for (.{ F17, BabyBear, KoalaBear, Goldilocks, Mersenne31, Mersenne61 }) |F| {
        const a = F.init(5);
        const b = F.init(3);

        // All operations should compile
        _ = a.add(b);
        _ = a.sub(b);
        _ = a.mul(b);
        _ = a.neg();
        _ = try a.inv();
        _ = try a.div(b);
        _ = a.pow(2);
    }
}

test "field_presets: large field arithmetic" {
    // Test with Goldilocks (largest 64-bit field)
    const a = Goldilocks.init(0xFFFFFFFEFFFFFFFF);
    const b = Goldilocks.init(0xFFFFFFFEFFFFFFFF);

    // Test multiplication of large values
    const prod = a.mul(b);

    // Result should be valid
    try testing.expect(prod.value < Goldilocks.MODULUS);

    // Test that a * a^(-1) = 1
    const inv_a = try a.inv();
    const unity = a.mul(inv_a);
    try testing.expect(unity.isOne());
}
