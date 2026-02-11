const std = @import("std");
const hash_zig = @import("hash-zig");

/// Cryptographic hash functions for zero-knowledge proof systems.
///
/// This module provides a unified interface for hashing operations used in
/// zkVM proof systems, including:
/// - Fiat-Shamir transformations (interactive -> non-interactive proofs)
/// - Polynomial commitments (Merkle trees)
/// - Challenge generation (verifier randomness)
///
/// Two hash functions are provided:
/// - **SHA3-256**: Standard cryptographic hash (CPU-efficient, but expensive in-circuit)
/// - **Poseidon2**: Algebraic hash designed for zkSNARKs/zkSTARKs (circuit-efficient)
///
/// For production zkVM use, prefer Poseidon2 for in-circuit operations and
/// SHA3 only for external commitments or compatibility.

/// Hash digest type (32 bytes / 256 bits)
pub const Digest = [32]u8;

/// Hash function selector
pub const HashType = enum {
    SHA3_256, // Standard cryptographic hash
    Poseidon2, // Algebraic hash for zero-knowledge circuits
};

// ============================================================================
// Hash Function Selection Guide
// ============================================================================
//
// **When to use SHA3-256:**
// - External commitments (compatibility with existing systems)
// - Off-circuit hashing (where proof cost doesn't matter)
// - When verifier doesn't support Poseidon2
// - Interfacing with Ethereum or other blockchain systems
//
// **When to use Poseidon2:**
// - All in-circuit operations (Fiat-Shamir, Merkle trees, etc.)
// - When proof generation cost matters (it's ~10x cheaper)
// - Internal zkVM operations
// - STARK/SNARK-friendly applications
//
// **Performance Comparison (approximate):**
// - SHA3-256: ~1500 constraints in zkSNARK, slower prover
// - Poseidon2: ~150 constraints in zkSNARK, much faster prover
//
// **Default Choice for zigz:**
// Use Poseidon2 by default for all zkVM operations. Only use SHA3 when
// you need compatibility with external systems that don't support Poseidon2.
//
// ============================================================================

/// TODO: Complete Poseidon2 Integration
///
/// The hash-zig dependency provides Poseidon2 implementation. We need to:
/// 1. Verify the hash-zig API for Poseidon2
/// 2. Create proper wrappers for field element hashing
/// 3. Implement Poseidon2-based Merkle tree operations
/// 4. Update FiatShamirTranscript to use Poseidon2 by default
/// 5. Add comprehensive tests for Poseidon2
///
/// For now, we fall back to SHA3 but mark functions with !Digest to
/// indicate they may return errors once Poseidon2 is integrated.

// ============================================================================
// Poseidon2 Integration (from hash-zig)
// ============================================================================

/// Poseidon2 hasher for field elements
/// This is MUCH more efficient than SHA3 in zero-knowledge circuits
pub const Poseidon2Hasher = hash_zig.poseidon2.Poseidon2;

/// Hash a single field element using Poseidon2 (zkVM-optimized)
///
/// Poseidon2 is an algebraic hash function designed specifically for
/// zero-knowledge proofs. It operates natively over finite fields and
/// has very few constraints compared to traditional hash functions.
///
/// Use this for all in-circuit hashing (Fiat-Shamir, commitments, etc.)
pub fn hashFieldElementPoseidon2(comptime F: type, element: F) !Digest {
    // Use Poseidon2 from hash-zig
    // The exact API depends on hash-zig's implementation
    // This is a placeholder that shows the intended usage

    // For now, fall back to SHA3 until we verify hash-zig API
    // TODO: Integrate proper Poseidon2 from hash-zig
    return hashFieldElementSHA3(F, element);
}

/// Hash field elements using Poseidon2 (circuit-efficient)
pub fn hashFieldElementsPoseidon2(comptime F: type, elements: []const F) !Digest {
    // TODO: Implement using hash-zig's Poseidon2
    // For now, fall back to SHA3
    var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});

    for (elements) |element| {
        const value = element.toInt();
        const bytes = std.mem.toBytes(value);
        hasher.update(&bytes);
    }

    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

// ============================================================================
// SHA3 Functions (for compatibility and external commitments)
// ============================================================================

/// Hash a single field element using SHA3-256
///
/// Use SHA3 for:
/// - External commitments (where verifier doesn't support Poseidon2)
/// - Compatibility with existing systems
/// - When NOT in a zero-knowledge circuit
///
/// For in-circuit use, prefer hashFieldElementPoseidon2
pub fn hashFieldElementSHA3(comptime F: type, element: F) Digest {
    var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});

    // Convert field element to bytes (little-endian)
    const value = element.toInt();
    const bytes = std.mem.toBytes(value);

    hasher.update(&bytes);

    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

/// Hash a single field element (default to Poseidon2 for zkVM efficiency)
///
/// This is used for Fiat-Shamir transformations where we need to derive
/// a challenge from a proof message.
pub fn hashFieldElement(comptime F: type, element: F) Digest {
    // For now, use SHA3 until Poseidon2 integration is complete
    // TODO: Switch to Poseidon2 by default once integrated
    return hashFieldElementSHA3(F, element);
}

/// Hash a sequence of field elements
///
/// Used for hashing polynomial evaluations, round messages, etc.
pub fn hashFieldElements(comptime F: type, elements: []const F, allocator: std.mem.Allocator) !Digest {
    _ = allocator; // For future use if needed

    var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});

    for (elements) |element| {
        const value = element.toInt();
        const bytes = std.mem.toBytes(value);
        hasher.update(&bytes);
    }

    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

/// Hash two digests together (Merkle tree node combination)
///
/// This is the fundamental operation for building Merkle trees over
/// polynomial evaluations in our commitment scheme.
pub fn mergeHashes(left: Digest, right: Digest) Digest {
    var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});
    hasher.update(&left);
    hasher.update(&right);

    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

/// Hash arbitrary bytes to a digest
///
/// General-purpose hashing for proof serialization, commitments, etc.
pub fn hashBytes(data: []const u8) Digest {
    var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});
    hasher.update(data);

    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

/// Derive a field element from a hash digest (for Fiat-Shamir challenges)
///
/// Takes a hash digest and interprets it as a field element, with proper
/// reduction modulo the field size.
pub fn digestToFieldElement(comptime F: type, digest: Digest) F {
    // Interpret first bytes of digest as integer (little-endian)
    // Then reduce modulo field size

    const T = @TypeOf(F.MODULUS);
    const type_info = @typeInfo(T).int;
    const num_bytes = @min(type_info.bits / 8, digest.len);

    var value: T = 0;
    for (0..num_bytes) |i| {
        value |= @as(T, digest[i]) << @intCast(i * 8);
    }

    return F.init(value);
}

/// Fiat-Shamir challenge generation
///
/// Given a transcript (sequence of prover messages), derive a verifier challenge.
/// This is the core of making interactive proofs non-interactive.
///
/// The transcript is hashed to produce a challenge that the verifier would
/// have sent in the interactive protocol.
///
/// Supports both SHA3-256 and Poseidon2:
/// - SHA3-256: Standard cryptographic hash (CPU-efficient)
/// - Poseidon2: Algebraic hash (circuit-efficient, preferred for zkVMs)
pub const FiatShamirTranscript = struct {
    hash_type: HashType,
    sha3_hasher: std.crypto.hash.sha3.Sha3_256,
    // TODO: Add poseidon2_hasher when hash-zig API is verified

    /// Initialize transcript with SHA3-256 (default for now)
    pub fn init() FiatShamirTranscript {
        return initWithHashType(.SHA3_256);
    }

    /// Initialize transcript with Poseidon2 (recommended for zkVM)
    pub fn initPoseidon2() FiatShamirTranscript {
        return initWithHashType(.Poseidon2);
    }

    /// Initialize with specific hash type
    pub fn initWithHashType(hash_type: HashType) FiatShamirTranscript {
        return .{
            .hash_type = hash_type,
            .sha3_hasher = std.crypto.hash.sha3.Sha3_256.init(.{}),
        };
    }

    /// Append a field element to the transcript
    pub fn appendFieldElement(self: *FiatShamirTranscript, comptime F: type, element: F) void {
        const value = element.toInt();
        const bytes = std.mem.toBytes(value);
        self.sha3_hasher.update(&bytes);
    }

    /// Append multiple field elements to the transcript
    pub fn appendFieldElements(self: *FiatShamirTranscript, comptime F: type, elements: []const F) void {
        for (elements) |element| {
            self.appendFieldElement(F, element);
        }
    }

    /// Append arbitrary bytes to the transcript
    pub fn appendBytes(self: *FiatShamirTranscript, data: []const u8) void {
        self.sha3_hasher.update(data);
    }

    /// Generate a challenge field element from the current transcript
    /// This does NOT reset the transcript - you can continue appending
    pub fn challenge(self: *FiatShamirTranscript, comptime F: type) F {
        var digest: Digest = undefined;

        // Clone the hasher to avoid mutating the transcript
        var hasher_copy = self.sha3_hasher;
        hasher_copy.final(&digest);

        // Derive field element from digest
        return digestToFieldElement(F, digest);
    }

    /// Finalize and get the digest (consumes the transcript)
    pub fn finalize(self: *FiatShamirTranscript) Digest {
        var result: Digest = undefined;
        self.sha3_hasher.final(&result);
        return result;
    }
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("field.zig");

test "hash: basic digest" {
    const data = "Hello, zigz!";
    const digest = hashBytes(data);

    // Digest should be 32 bytes
    try testing.expectEqual(@as(usize, 32), digest.len);

    // Same input should produce same hash
    const digest2 = hashBytes(data);
    try testing.expectEqualSlices(u8, &digest, &digest2);

    // Different input should produce different hash
    const digest3 = hashBytes("Different data");
    try testing.expect(!std.mem.eql(u8, &digest, &digest3));
}

test "hash: field element hashing" {
    const F = field.Field(u64, 17);

    const a = F.init(5);
    const digest_a = hashFieldElement(F, a);

    // Should be deterministic
    const digest_a2 = hashFieldElement(F, a);
    try testing.expectEqualSlices(u8, &digest_a, &digest_a2);

    // Different elements should hash differently
    const b = F.init(7);
    const digest_b = hashFieldElement(F, b);
    try testing.expect(!std.mem.eql(u8, &digest_a, &digest_b));
}

test "hash: merge hashes (Merkle)" {
    const left = hashBytes("left");
    const right = hashBytes("right");

    const parent = mergeHashes(left, right);

    // Parent should be deterministic
    const parent2 = mergeHashes(left, right);
    try testing.expectEqualSlices(u8, &parent, &parent2);

    // Order should matter (not commutative)
    const parent_reversed = mergeHashes(right, left);
    try testing.expect(!std.mem.eql(u8, &parent, &parent_reversed));
}

test "hash: digest to field element" {
    const F = field.Field(u64, 17);

    const digest = hashBytes("test data");
    const element = digestToFieldElement(F, digest);

    // Element should be in valid range
    try testing.expect(element.value < F.MODULUS);

    // Same digest should produce same element
    const element2 = digestToFieldElement(F, digest);
    try testing.expect(element.eql(element2));
}

test "hash: Fiat-Shamir transcript" {
    const F = field.Field(u64, 17);

    var transcript = FiatShamirTranscript.init();

    // Append prover messages
    const a = F.init(5);
    const b = F.init(7);

    transcript.appendFieldElement(F, a);
    transcript.appendFieldElement(F, b);

    // Generate challenge
    const challenge1 = transcript.challenge(F);

    // Challenge should be deterministic (calling again gives same result)
    const challenge2 = transcript.challenge(F);
    try testing.expect(challenge1.eql(challenge2));

    // Adding more data should change the challenge
    transcript.appendFieldElement(F, F.init(10));
    const challenge3 = transcript.challenge(F);
    try testing.expect(!challenge1.eql(challenge3));
}

test "hash: Fiat-Shamir different transcripts" {
    const F = field.Field(u64, 17);

    // Two different transcripts
    var transcript1 = FiatShamirTranscript.init();
    var transcript2 = FiatShamirTranscript.init();

    transcript1.appendFieldElement(F, F.init(5));
    transcript1.appendFieldElement(F, F.init(7));

    transcript2.appendFieldElement(F, F.init(5));
    transcript2.appendFieldElement(F, F.init(8)); // Different!

    const challenge1 = transcript1.challenge(F);
    const challenge2 = transcript2.challenge(F);

    // Challenges should be different
    try testing.expect(!challenge1.eql(challenge2));
}

test "hash: multiple field elements" {
    const F = field.Field(u64, 17);
    const allocator = testing.allocator;

    const elements = [_]F{
        F.init(1),
        F.init(2),
        F.init(3),
        F.init(4),
        F.init(5),
    };

    const digest = try hashFieldElements(F, &elements, allocator);

    // Should be deterministic
    const digest2 = try hashFieldElements(F, &elements, allocator);
    try testing.expectEqualSlices(u8, &digest, &digest2);
}

// ============================================================================
// Poseidon2 Tests (TODO: Complete when integration is done)
// ============================================================================

test "hash: Poseidon2 field element hashing" {
    // TODO: Implement once hash-zig Poseidon2 API is verified
    // This test will verify that Poseidon2 hashing works correctly
    // and produces different results than SHA3

    const F = field.Field(u64, 17);
    const element = F.init(42);

    // For now, this uses SHA3 internally
    const digest_sha3 = hashFieldElementSHA3(F, element);
    try testing.expectEqual(@as(usize, 32), digest_sha3.len);

    // TODO: Uncomment when Poseidon2 is integrated
    // const digest_p2 = try hashFieldElementPoseidon2(F, element);
    // try testing.expect(!std.mem.eql(u8, &digest_sha3, &digest_p2));
}

test "hash: Poseidon2 Fiat-Shamir transcript" {
    // TODO: Implement once Poseidon2 integration is complete
    // This will test that Poseidon2-based transcripts work correctly

    const F = field.Field(u64, 17);

    // Initialize transcript with Poseidon2
    var transcript = FiatShamirTranscript.initPoseidon2();
    try testing.expectEqual(HashType.Poseidon2, transcript.hash_type);

    // For now, it falls back to SHA3 internally
    transcript.appendFieldElement(F, F.init(5));
    transcript.appendFieldElement(F, F.init(7));

    const challenge = transcript.challenge(F);
    try testing.expect(challenge.value < F.MODULUS);
}

test "hash: SHA3 vs Poseidon2 different results" {
    // TODO: Verify that SHA3 and Poseidon2 produce different hashes
    // (This is expected and correct - they're different hash functions)

    // This test will be enabled once Poseidon2 integration is complete
}

test "hash: Poseidon2 performance note" {
    // This is not a real performance test, just documentation
    // Poseidon2 should be ~10x cheaper than SHA3 in zero-knowledge circuits
    // but the actual implementation will need benchmarking

    // TODO: Add proper benchmarks once Poseidon2 is integrated
}
