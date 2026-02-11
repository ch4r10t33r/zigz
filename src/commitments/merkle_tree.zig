const std = @import("std");
const hash = @import("../core/hash.zig");

/// Binary Merkle Tree for Polynomial Commitments
///
/// A Merkle tree commits to a vector of field elements (polynomial evaluations)
/// using cryptographic hashing. The commitment is the root hash.
///
/// **Properties:**
/// - Commitment size: 32 bytes (regardless of data size)
/// - Opening proof size: O(log n) hashes
/// - Transparent: no trusted setup
/// - Post-quantum secure (relies only on hash functions)
///
/// **Hash Functions:**
/// - SHA3-256: Standard cryptographic hash (CPU-efficient)
/// - Poseidon2: Algebraic hash (circuit-efficient, recommended for zkVM)
///
/// **Usage:**
/// 1. Build tree from polynomial evaluations
/// 2. Commitment = root hash
/// 3. To prove evaluation at index i: provide value + Merkle path
/// 4. Verifier checks: hash up from leaf → root

pub const HASH_SIZE = 32;
pub const Hash = [HASH_SIZE]u8;

/// Merkle tree node
pub const Node = struct {
    hash: Hash,
    left: ?*Node,
    right: ?*Node,

    pub fn isLeaf(self: Node) bool {
        return self.left == null and self.right == null;
    }
};

/// Merkle path for opening proof
pub const MerklePath = struct {
    siblings: []Hash,
    directions: []bool, // false = left, true = right
    allocator: std.mem.Allocator,

    const Self = @This();

    pub fn init(allocator: std.mem.Allocator, height: usize) !Self {
        const siblings = try allocator.alloc(Hash, height);
        const directions = try allocator.alloc(bool, height);
        return Self{
            .siblings = siblings,
            .directions = directions,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: Self) void {
        self.allocator.free(self.siblings);
        self.allocator.free(self.directions);
    }
};

/// Opening proof: value + Merkle path
pub fn OpeningProof(comptime F: type) type {
    return struct {
        index: usize,
        value: F,
        path: MerklePath,

        const Self = @This();

        pub fn deinit(self: Self) void {
            self.path.deinit();
        }
    };
}

/// Binary Merkle tree
pub fn MerkleTree(comptime F: type) type {
    return struct {
        root: *Node,
        leaves: []Hash,
        height: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        /// Build Merkle tree from field elements
        pub fn build(values: []const F, allocator: std.mem.Allocator) !Self {
            if (values.len == 0) return error.EmptyValues;

            // Pad to power of 2
            const padded_len = std.math.ceilPowerOfTwo(usize, values.len) catch return error.TooManyValues;
            const height = std.math.log2(padded_len);

            // Create leaf hashes
            var leaves = try allocator.alloc(Hash, padded_len);
            errdefer allocator.free(leaves);

            for (values, 0..) |val, i| {
                leaves[i] = hashLeaf(F, val);
            }

            // Pad with zero hashes
            const zero_hash = hashLeaf(F, F.zero());
            for (values.len..padded_len) |i| {
                leaves[i] = zero_hash;
            }

            // Build tree bottom-up
            const root = try buildRecursive(leaves, allocator);

            return Self{
                .root = root,
                .leaves = leaves,
                .height = height,
                .allocator = allocator,
            };
        }

        /// Get root hash (commitment)
        pub fn root_hash(self: Self) Hash {
            return self.root.hash;
        }

        /// Generate opening proof for index
        pub fn open(self: Self, index: usize) !OpeningProof(F) {
            if (index >= self.leaves.len) return error.IndexOutOfBounds;

            var path = try MerklePath.init(self.allocator, self.height);
            errdefer path.deinit();

            // Traverse from leaf to root, collecting siblings
            var current_index = index;
            var level_start: usize = 0;
            var level_size = self.leaves.len;

            for (0..self.height) |level| {
                const is_right = (current_index % 2) == 1;
                const sibling_index = if (is_right) current_index - 1 else current_index + 1;

                // Get sibling hash
                path.siblings[level] = try self.getSiblingHash(level, level_start + sibling_index, level_size);
                path.directions[level] = is_right;

                // Move up to parent
                current_index = current_index / 2;
                level_start += level_size;
                level_size = level_size / 2;
            }

            // Reconstruct value from leaf hash
            const value = try self.getValueAtIndex(index);

            return OpeningProof(F){
                .index = index,
                .value = value,
                .path = path,
            };
        }

        /// Verify opening proof
        pub fn verify(root: Hash, proof: OpeningProof(F)) bool {
            var current_hash = hashLeaf(F, proof.value);

            // Hash up the path
            for (proof.path.siblings, proof.path.directions) |sibling, is_right| {
                current_hash = if (is_right)
                    hashInternal(sibling, current_hash)
                else
                    hashInternal(current_hash, sibling);
            }

            return std.mem.eql(u8, &current_hash, &root);
        }

        pub fn deinit(self: Self) void {
            self.allocator.free(self.leaves);
            self.freeNode(self.root);
        }

        fn freeNode(self: Self, node: *Node) void {
            if (node.left) |left| self.freeNode(left);
            if (node.right) |right| self.freeNode(right);
            self.allocator.destroy(node);
        }

        fn buildRecursive(hashes: []const Hash, allocator: std.mem.Allocator) !*Node {
            if (hashes.len == 1) {
                // Leaf node
                const node = try allocator.create(Node);
                node.* = Node{
                    .hash = hashes[0],
                    .left = null,
                    .right = null,
                };
                return node;
            }

            // Split in half
            const mid = hashes.len / 2;
            const left_hashes = hashes[0..mid];
            const right_hashes = hashes[mid..];

            const left = try buildRecursive(left_hashes, allocator);
            errdefer allocator.destroy(left);

            const right = try buildRecursive(right_hashes, allocator);
            errdefer allocator.destroy(right);

            // Create parent node
            const node = try allocator.create(Node);
            node.* = Node{
                .hash = hashInternal(left.hash, right.hash),
                .left = left,
                .right = right,
            };

            return node;
        }

        fn getSiblingHash(self: Self, level: usize, index: usize, level_size: usize) !Hash {
            if (level == 0) {
                // Bottom level - leaves
                if (index >= self.leaves.len) return error.IndexOutOfBounds;
                return self.leaves[index];
            }

            // Higher levels - compute from tree structure
            // For simplicity, we traverse the tree
            // (In production, might cache intermediate hashes)
            _ = level_size;
            _ = index;
            // Simplified: return zero hash for now
            // Full implementation would traverse tree to get actual hash
            return hashLeaf(F, F.zero());
        }

        fn getValueAtIndex(self: Self, index: usize) !F {
            // In a real implementation, we'd store original values
            // For now, this is a simplified version
            _ = self;
            _ = index;
            return error.NotImplemented;
        }

        /// Hash a leaf value
        fn hashLeaf(comptime T: type, value: T) Hash {
            var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});
            hasher.update(std.mem.asBytes(&value.value));
            var hash: Hash = undefined;
            hasher.final(&hash);
            return hash;
        }

        /// Hash two internal nodes
        fn hashInternal(left: Hash, right: Hash) Hash {
            var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});
            hasher.update(&left);
            hasher.update(&right);
            var hash: Hash = undefined;
            hasher.final(&hash);
            return hash;
        }
    };
}

// ============================================================================
// Simplified Implementation for Testing
// ============================================================================

/// Simplified Merkle tree that stores values for testing
///
/// Generic over hash function type for flexibility
pub fn SimpleMerkleTree(comptime F: type, comptime HashFn: type) type {
    return struct {
        root_hash: Hash,
        values: []F,
        leaf_hashes: []Hash,
        height: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn build(values: []const F, allocator: std.mem.Allocator) !Self {
            if (values.len == 0) return error.EmptyValues;

            // Pad to power of 2
            const padded_len = std.math.ceilPowerOfTwo(usize, values.len) catch return error.TooManyValues;
            const height = std.math.log2(padded_len);

            // Store values
            const stored_values = try allocator.dupe(F, values);
            errdefer allocator.free(stored_values);

            // Create leaf hashes
            var leaf_hashes = try allocator.alloc(Hash, padded_len);
            errdefer allocator.free(leaf_hashes);

            for (values, 0..) |val, i| {
                leaf_hashes[i] = HashFn.hashLeaf(F, val);
            }

            // Pad with zero hashes
            const zero_hash = HashFn.hashLeaf(F, F.zero());
            for (values.len..padded_len) |i| {
                leaf_hashes[i] = zero_hash;
            }

            // Build tree bottom-up to get root
            const root = try computeRoot(leaf_hashes, allocator);

            return Self{
                .root_hash = root,
                .values = stored_values,
                .leaf_hashes = leaf_hashes,
                .height = height,
                .allocator = allocator,
            };
        }

        pub fn getRoot(self: Self) Hash {
            return self.root_hash;
        }

        pub fn open(self: Self, index: usize) !OpeningProof(F) {
            if (index >= self.values.len) return error.IndexOutOfBounds;

            var path = try MerklePath.init(self.allocator, self.height);
            errdefer path.deinit();

            // Build path from leaf to root
            var current_index = index;
            var current_level = try self.allocator.dupe(Hash, self.leaf_hashes);
            defer self.allocator.free(current_level);

            for (0..self.height) |level| {
                const is_right = (current_index % 2) == 1;
                const sibling_index = if (is_right) current_index - 1 else current_index + 1;

                path.siblings[level] = current_level[sibling_index];
                path.directions[level] = is_right;

                // Compute next level
                const next_size = current_level.len / 2;
                var next_level = try self.allocator.alloc(Hash, next_size);

                for (0..next_size) |i| {
                    next_level[i] = HashFn.hashInternal(current_level[i * 2], current_level[i * 2 + 1]);
                }

                self.allocator.free(current_level);
                current_level = next_level;
                current_index = current_index / 2;
            }

            return OpeningProof(F){
                .index = index,
                .value = self.values[index],
                .path = path,
            };
        }

        pub fn verify(root: Hash, proof: OpeningProof(F)) bool {
            var current_hash = HashFn.hashLeaf(F, proof.value);

            for (proof.path.siblings, proof.path.directions) |sibling, is_right| {
                current_hash = if (is_right)
                    HashFn.hashInternal(sibling, current_hash)
                else
                    HashFn.hashInternal(current_hash, sibling);
            }

            return std.mem.eql(u8, &current_hash, &root);
        }

        pub fn deinit(self: Self) void {
            self.allocator.free(self.values);
            self.allocator.free(self.leaf_hashes);
        }

        fn computeRoot(hashes: []const Hash, allocator: std.mem.Allocator) !Hash {
            if (hashes.len == 1) return hashes[0];

            var current_level = try allocator.dupe(Hash, hashes);
            defer allocator.free(current_level);

            while (current_level.len > 1) {
                const next_size = current_level.len / 2;
                var next_level = try allocator.alloc(Hash, next_size);

                for (0..next_size) |i| {
                    next_level[i] = HashFn.hashInternal(current_level[i * 2], current_level[i * 2 + 1]);
                }

                allocator.free(current_level);
                current_level = next_level;
            }

            const root = current_level[0];
            return root;
        }
    };
}

// ============================================================================
// Type Aliases for Convenience
// ============================================================================

/// Merkle tree using SHA3-256 (standard cryptographic hash)
pub fn MerkleTreeSHA3(comptime F: type) type {
    return SimpleMerkleTree(F, hash.SHA3Hasher);
}

/// Merkle tree using Poseidon2 (circuit-efficient, recommended for zkVM)
pub fn MerkleTreePoseidon2(comptime F: type) type {
    return SimpleMerkleTree(F, hash.Poseidon2GenericHasher);
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "merkle_tree: simple tree build SHA3" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    const values = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    try testing.expectEqual(@as(usize, 2), tree.height);
    try testing.expectEqual(@as(usize, 4), tree.values.len);
}

test "merkle_tree: root commitment determinism" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    const values = [_]F{ F.init(5), F.init(7), F.init(11), F.init(13) };

    var tree1 = try Tree.build(&values, testing.allocator);
    defer tree1.deinit();

    var tree2 = try Tree.build(&values, testing.allocator);
    defer tree2.deinit();

    // Same values should produce same root
    try testing.expect(std.mem.eql(u8, &tree1.getRoot(), &tree2.getRoot()));
}

test "merkle_tree: opening proof" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    const values = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    // Open at index 2
    var proof = try tree.open(2);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 2), proof.index);
    try testing.expect(proof.value.eql(F.init(3)));
    try testing.expectEqual(@as(usize, 2), proof.path.siblings.len);
}

test "merkle_tree: valid proof verifies" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    const values = [_]F{ F.init(10), F.init(20), F.init(30), F.init(40) };
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    const root = tree.getRoot();

    // Open and verify each index
    for (0..values.len) |i| {
        var proof = try tree.open(i);
        defer proof.deinit();

        const is_valid = Tree.verify(root, proof);
        try testing.expect(is_valid);
    }
}

test "merkle_tree: invalid proof rejected" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    const values = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    const root = tree.getRoot();

    var proof = try tree.open(1);
    defer proof.deinit();

    // Tamper with value
    proof.value = F.init(99);

    const is_valid = Tree.verify(root, proof);
    try testing.expect(!is_valid);
}

test "merkle_tree: non-power-of-2 padding" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    // 5 values (not power of 2)
    const values = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4), F.init(5) };
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    // Should pad to 8 (next power of 2)
    try testing.expectEqual(@as(usize, 3), tree.height); // log2(8) = 3

    // Verify all original values
    for (0..values.len) |i| {
        var proof = try tree.open(i);
        defer proof.deinit();

        try testing.expect(Tree.verify(tree.getRoot(), proof));
    }
}

test "merkle_tree: single value" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    const values = [_]F{F.init(42)};
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    try testing.expectEqual(@as(usize, 0), tree.height);

    var proof = try tree.open(0);
    defer proof.deinit();

    try testing.expect(Tree.verify(tree.getRoot(), proof));
}

test "merkle_tree: proof size logarithmic" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreeSHA3(F);

    // Test different sizes
    const sizes = [_]usize{ 4, 8, 16, 32, 64 };

    for (sizes) |size| {
        var values = try testing.allocator.alloc(F, size);
        defer testing.allocator.free(values);

        for (values, 0..) |*v, i| {
            v.* = F.init(@intCast(i));
        }

        var tree = try Tree.build(values, testing.allocator);
        defer tree.deinit();

        var proof = try tree.open(0);
        defer proof.deinit();

        const expected_height = std.math.log2(size);
        try testing.expectEqual(expected_height, proof.path.siblings.len);
    }
}

// ============================================================================
// Poseidon2 Tests
// ============================================================================

test "merkle_tree: Poseidon2 build and verify" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreePoseidon2(F);

    const values = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var tree = try Tree.build(&values, testing.allocator);
    defer tree.deinit();

    // Open and verify
    var proof = try tree.open(2);
    defer proof.deinit();

    const is_valid = Tree.verify(tree.getRoot(), proof);
    try testing.expect(is_valid);
}

test "merkle_tree: SHA3 vs Poseidon2 different roots" {
    const F = field.Field(u64, 17);

    const values = [_]F{ F.init(10), F.init(20), F.init(30), F.init(40) };

    var tree_sha3 = try MerkleTreeSHA3(F).build(&values, testing.allocator);
    defer tree_sha3.deinit();

    var tree_p2 = try MerkleTreePoseidon2(F).build(&values, testing.allocator);
    defer tree_p2.deinit();

    const root_sha3 = tree_sha3.getRoot();
    const root_p2 = tree_p2.getRoot();

    // Different hash functions should produce different roots
    try testing.expect(!std.mem.eql(u8, &root_sha3, &root_p2));
}

test "merkle_tree: Poseidon2 determinism" {
    const F = field.Field(u64, 17);
    const Tree = MerkleTreePoseidon2(F);

    const values = [_]F{ F.init(5), F.init(7), F.init(11), F.init(13) };

    var tree1 = try Tree.build(&values, testing.allocator);
    defer tree1.deinit();

    var tree2 = try Tree.build(&values, testing.allocator);
    defer tree2.deinit();

    // Same values should produce same root
    try testing.expect(std.mem.eql(u8, &tree1.getRoot(), &tree2.getRoot()));
}
