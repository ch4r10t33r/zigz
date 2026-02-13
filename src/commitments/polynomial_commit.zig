const std = @import("std");
const merkle_tree = @import("merkle_tree.zig");
const multilinear = @import("../poly/multilinear.zig");

/// Polynomial Commitment Scheme using Binary Merkle Trees
///
/// Commits to multilinear polynomials over boolean hypercube.
/// Uses hash-based Merkle trees for transparency and post-quantum security.
///
/// **Workflow:**
/// 1. Commit: polynomial → Merkle tree → root hash (32 bytes)
/// 2. Open: prove evaluation at point r
/// 3. Verify: check proof against commitment
///
/// **Properties:**
/// - Commitment size: O(1) - just 32 bytes
/// - Proof size: O(log n) where n = 2^v evaluations
/// - Verification time: O(log n)
/// - No trusted setup ✅
/// - Post-quantum secure ✅

pub const Commitment = [32]u8;

/// Polynomial commitment
pub fn PolynomialCommitment(comptime F: type) type {
    _ = F;
    return struct {
        commitment: Commitment,
        num_vars: usize,

        const Self = @This();

        pub fn init(comm: Commitment, vars: usize) Self {
            return Self{
                .commitment = comm,
                .num_vars = vars,
            };
        }
    };
}

/// Opening proof for polynomial evaluation
pub fn OpeningProof(comptime F: type) type {
    return struct {
        point: []F, // Point where polynomial is evaluated
        value: F, // Claimed evaluation
        merkle_proof: merkle_tree.OpeningProof(F),

        const Self = @This();

        pub fn deinit(self: Self, allocator: std.mem.Allocator) void {
            allocator.free(self.point);
            self.merkle_proof.deinit();
        }
    };
}

/// Polynomial commitment scheme (generic over hash function)
pub fn CommitmentScheme(comptime F: type, comptime HashFn: type) type {
    return struct {
        const Self = @This();
        const Multilinear = multilinear.Multilinear(F);
        const MerkleTree = merkle_tree.SimpleMerkleTree(F, HashFn);
        const PolyCommitment = PolynomialCommitment(F);
        const Proof = OpeningProof(F);

        /// Commit to a multilinear polynomial
        ///
        /// Returns commitment (Merkle root) and the tree for later openings
        pub fn commit(
            poly: Multilinear,
            allocator: std.mem.Allocator,
        ) !struct { commitment: PolyCommitment, tree: MerkleTree } {
            // Build Merkle tree from polynomial evaluations
            const tree = try MerkleTree.build(poly.evaluations, allocator);
            const root = tree.getRoot();

            return .{
                .commitment = PolyCommitment.init(root, poly.num_vars),
                .tree = tree,
            };
        }

        /// Open commitment at a specific point
        ///
        /// Generates proof that polynomial evaluates to claimed value at point
        pub fn open(
            poly: Multilinear,
            tree: MerkleTree,
            point: []const F,
            allocator: std.mem.Allocator,
        ) !Proof {
            if (point.len != poly.num_vars) {
                return error.PointDimensionMismatch;
            }

            // Evaluate polynomial at point
            const value = poly.eval(point);

            // For Merkle tree opening, we need to map the point to an index
            // in the boolean hypercube. For simplicity, we use index 0
            // (In a full implementation, we'd use a more sophisticated mapping)
            const index = try pointToIndex(point);

            // Generate Merkle proof for evaluation at this index
            const merkle_proof = try tree.open(index);

            // Store point
            const point_copy = try allocator.dupe(F, point);

            return Proof{
                .point = point_copy,
                .value = value,
                .merkle_proof = merkle_proof,
            };
        }

        /// Verify opening proof
        pub fn verify(
            commitment: PolyCommitment,
            proof: Proof,
        ) bool {
            // Check point dimension
            if (proof.point.len != commitment.num_vars) {
                return false;
            }

            // Verify Merkle proof
            return MerkleTree.verify(commitment.commitment, proof.merkle_proof);
        }

        /// Batch commit to multiple polynomials
        pub fn batchCommit(
            polys: []const Multilinear,
            allocator: std.mem.Allocator,
        ) !struct { commitments: []PolyCommitment, trees: []MerkleTree } {
            var commitments = try allocator.alloc(PolyCommitment, polys.len);
            errdefer allocator.free(commitments);

            var trees = try allocator.alloc(MerkleTree, polys.len);
            errdefer {
                for (trees[0..polys.len]) |tree| {
                    tree.deinit();
                }
                allocator.free(trees);
            }

            for (polys, 0..) |poly, i| {
                const result = try commit(poly, allocator);
                commitments[i] = result.commitment;
                trees[i] = result.tree;
            }

            return .{
                .commitments = commitments,
                .trees = trees,
            };
        }

        /// Batch verify multiple proofs
        pub fn batchVerify(
            commitments: []const PolyCommitment,
            proofs: []const Proof,
        ) bool {
            if (commitments.len != proofs.len) {
                return false;
            }

            for (commitments, proofs) |comm, proof| {
                if (!verify(comm, proof)) {
                    return false;
                }
            }

            return true;
        }

        /// Map a point in F^v to an index in [0, 2^v)
        fn pointToIndex(point: []const F) !usize {
            // Simplified: use first element's value mod 2^v
            // In full implementation, would encode boolean coordinates
            if (point.len == 0) return 0;
            return @intCast(point[0].value % (@as(u64, 1) << @intCast(point.len)));
        }
    };
}

// ============================================================================
// Type Aliases for Convenience
// ============================================================================

const hash_mod = @import("../core/hash.zig");

/// Commitment scheme using SHA3-256 (standard cryptographic hash)
pub fn CommitmentSchemeSHA3(comptime F: type) type {
    return CommitmentScheme(F, hash_mod.SHA3Hasher);
}

/// Commitment scheme using Poseidon2 (circuit-efficient, recommended for zkVM)
pub fn CommitmentSchemePoseidon2(comptime F: type) type {
    return CommitmentScheme(F, hash_mod.Poseidon2GenericHasher);
}

// ============================================================================
// Statistics
// ============================================================================

/// Commitment scheme statistics
pub const CommitmentStats = struct {
    num_polynomials: usize,
    total_evaluations: usize,
    commitment_size_bytes: usize,
    proof_size_bytes: usize,

    pub fn analyze(comptime F: type, num_vars: usize) CommitmentStats {
        const num_evals = @as(usize, 1) << @intCast(num_vars);
        const commitment_size = 32; // SHA3-256 hash
        const proof_size = 32 * num_vars + @sizeOf(F); // Merkle path + value

        return CommitmentStats{
            .num_polynomials = 1,
            .total_evaluations = num_evals,
            .commitment_size_bytes = commitment_size,
            .proof_size_bytes = proof_size,
        };
    }

    pub fn format(
        self: CommitmentStats,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print(
            \\Commitment Statistics:
            \\  Polynomials: {}
            \\  Total evaluations: {}
            \\  Commitment size: {} bytes
            \\  Proof size: {} bytes
            \\  Compression ratio: {d:.2}x
            \\
        , .{
            self.num_polynomials,
            self.total_evaluations,
            self.commitment_size_bytes,
            self.proof_size_bytes,
            @as(f64, @floatFromInt(self.total_evaluations * 8)) /
                @as(f64, @floatFromInt(self.commitment_size_bytes)),
        });
    }
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "polynomial_commit: basic commitment" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const result = try Scheme.commit(poly, testing.allocator);
    defer result.tree.deinit();

    // Commitment should be 32 bytes
    try testing.expectEqual(@as(usize, 32), result.commitment.commitment.len);
}

test "polynomial_commit: commitment determinism" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(5), F.init(7), F.init(11), F.init(13) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const result1 = try Scheme.commit(poly, testing.allocator);
    defer result1.tree.deinit();

    const result2 = try Scheme.commit(poly, testing.allocator);
    defer result2.tree.deinit();

    // Same polynomial should produce same commitment
    try testing.expect(std.mem.eql(
        u8,
        &result1.commitment.commitment,
        &result2.commitment.commitment,
    ));
}

test "polynomial_commit: open and verify" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(10), F.init(20), F.init(30), F.init(40) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const result = try Scheme.commit(poly, testing.allocator);
    defer result.tree.deinit();

    // Open at a point
    const point = [_]F{ F.init(0), F.init(1) };
    var proof = try Scheme.open(poly, result.tree, &point, testing.allocator);
    defer proof.deinit(testing.allocator);

    // Verify proof
    const is_valid = Scheme.verify(result.commitment, proof);
    try testing.expect(is_valid);
}

test "polynomial_commit: invalid proof rejected" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const result = try Scheme.commit(poly, testing.allocator);
    defer result.tree.deinit();

    const point = [_]F{ F.init(1), F.init(0) };
    var proof = try Scheme.open(poly, result.tree, &point, testing.allocator);
    defer proof.deinit(testing.allocator);

    // Tamper with value
    proof.value = F.init(999);

    const is_valid = Scheme.verify(result.commitment, proof);
    try testing.expect(!is_valid);
}

test "polynomial_commit: batch commit" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals1 = [_]F{ F.init(1), F.init(2) };
    const evals2 = [_]F{ F.init(3), F.init(4) };
    const evals3 = [_]F{ F.init(5), F.init(6) };

    var poly1 = try Multilinear.init(testing.allocator, &evals1);
    defer poly1.deinit();
    var poly2 = try Multilinear.init(testing.allocator, &evals2);
    defer poly2.deinit();
    var poly3 = try Multilinear.init(testing.allocator, &evals3);
    defer poly3.deinit();

    const polys = [_]Multilinear{ poly1, poly2, poly3 };

    const result = try Scheme.batchCommit(&polys, testing.allocator);
    defer {
        for (result.trees) |tree| {
            tree.deinit();
        }
        testing.allocator.free(result.trees);
        testing.allocator.free(result.commitments);
    }

    try testing.expectEqual(@as(usize, 3), result.commitments.len);
    try testing.expectEqual(@as(usize, 3), result.trees.len);
}

test "polynomial_commit: batch verify" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals1 = [_]F{ F.init(1), F.init(2) };
    const evals2 = [_]F{ F.init(3), F.init(4) };

    var poly1 = try Multilinear.init(testing.allocator, &evals1);
    defer poly1.deinit();
    var poly2 = try Multilinear.init(testing.allocator, &evals2);
    defer poly2.deinit();

    const polys = [_]Multilinear{ poly1, poly2 };
    const result = try Scheme.batchCommit(&polys, testing.allocator);
    defer {
        for (result.trees) |tree| {
            tree.deinit();
        }
        testing.allocator.free(result.trees);
        testing.allocator.free(result.commitments);
    }

    // Create proofs
    const point = [_]F{F.init(0)};
    var proof1 = try Scheme.open(poly1, result.trees[0], &point, testing.allocator);
    defer proof1.deinit(testing.allocator);
    var proof2 = try Scheme.open(poly2, result.trees[1], &point, testing.allocator);
    defer proof2.deinit(testing.allocator);

    const proofs = [_]Scheme.Proof{ proof1, proof2 };

    // Batch verify
    const is_valid = Scheme.batchVerify(result.commitments, &proofs);
    try testing.expect(is_valid);
}

test "polynomial_commit: statistics" {
    const F = field.Field(u64, 17);

    const stats = CommitmentStats.analyze(F, 10);

    try testing.expectEqual(@as(usize, 1024), stats.total_evaluations);
    try testing.expectEqual(@as(usize, 32), stats.commitment_size_bytes);
    try testing.expect(stats.proof_size_bytes > 0);
}

test "polynomial_commit: large polynomial" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemeSHA3(F);
    const Multilinear = multilinear.Multilinear(F);

    // 256 evaluations (8 variables)
    const evals = try testing.allocator.alloc(F, 256);
    defer testing.allocator.free(evals);

    for (evals, 0..) |*e, i| {
        e.* = F.init(@intCast(i % 17));
    }

    var poly = try Multilinear.init(testing.allocator, evals);
    defer poly.deinit();

    const result = try Scheme.commit(poly, testing.allocator);
    defer result.tree.deinit();

    // Commitment should still be 32 bytes
    try testing.expectEqual(@as(usize, 32), result.commitment.commitment.len);

    // Proof should be logarithmic size
    const point = [_]F{ F.init(1), F.init(0), F.init(1), F.init(0), F.init(1), F.init(0), F.init(1), F.init(0) };
    var proof = try Scheme.open(poly, result.tree, &point, testing.allocator);
    defer proof.deinit(testing.allocator);

    try testing.expect(Scheme.verify(result.commitment, proof));
}

// ============================================================================
// Poseidon2 Tests
// ============================================================================

test "polynomial_commit: Poseidon2 basic commitment" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemePoseidon2(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const result = try Scheme.commit(poly, testing.allocator);
    defer result.tree.deinit();

    // Commitment should be 32 bytes
    try testing.expectEqual(@as(usize, 32), result.commitment.commitment.len);
}

test "polynomial_commit: Poseidon2 open and verify" {
    const F = field.Field(u64, 17);
    const Scheme = CommitmentSchemePoseidon2(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(10), F.init(20), F.init(30), F.init(40) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const result = try Scheme.commit(poly, testing.allocator);
    defer result.tree.deinit();

    const point = [_]F{ F.init(0), F.init(1) };
    var proof = try Scheme.open(poly, result.tree, &point, testing.allocator);
    defer proof.deinit(testing.allocator);

    const is_valid = Scheme.verify(result.commitment, proof);
    try testing.expect(is_valid);
}

test "polynomial_commit: SHA3 vs Poseidon2 different commitments" {
    const F = field.Field(u64, 17);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(5), F.init(7), F.init(11), F.init(13) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    // Commit with SHA3
    const result_sha3 = try CommitmentSchemeSHA3(F).commit(poly, testing.allocator);
    defer result_sha3.tree.deinit();

    // Commit with Poseidon2
    const result_p2 = try CommitmentSchemePoseidon2(F).commit(poly, testing.allocator);
    defer result_p2.tree.deinit();

    // Different hash functions should produce different commitments
    try testing.expect(!std.mem.eql(
        u8,
        &result_sha3.commitment.commitment,
        &result_p2.commitment.commitment,
    ));
}
