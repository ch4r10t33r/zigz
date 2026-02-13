const std = @import("std");
const field = @import("../core/field.zig");
const multilinear = @import("../poly/multilinear.zig");
const sumcheck_protocol = @import("../proofs/sumcheck_protocol.zig");
const polynomial_commit = @import("../commitments/polynomial_commit.zig");

/// Proof Structure for zigz zkVM
///
/// A complete proof consists of:
/// 1. Sumcheck proof for constraint satisfaction
/// 2. Lasso lookup proofs for instruction tables
/// 3. Polynomial commitments and openings
/// 4. Public inputs and outputs
///
/// The proof size is O(log n) where n is the number of execution steps.

/// Public inputs and outputs for the program
pub const PublicIO = struct {
    /// Program hash (commitment to the bytecode)
    program_hash: [32]u8,

    /// Initial program counter
    initial_pc: u64,

    /// Initial register values (if any are public)
    initial_regs: ?[]const u64,

    /// Final program counter (proves execution halted)
    final_pc: u64,

    /// Final register values (public outputs)
    final_regs: ?[]const u64,

    /// Number of execution steps
    num_steps: usize,

    /// Memory initialization (sparse representation)
    initial_memory: ?std.AutoHashMap(u64, u8),

    pub fn deinit(self: *PublicIO, allocator: std.mem.Allocator) void {
        if (self.initial_regs) |regs| allocator.free(regs);
        if (self.final_regs) |regs| allocator.free(regs);
        if (self.initial_memory) |*mem| mem.deinit();
    }
};

/// Sumcheck proof component
pub fn SumcheckProof(comptime F: type) type {
    return struct {
        const Self = @This();

        /// Number of variables in the polynomial
        num_vars: usize,

        /// Round polynomials (one per variable)
        /// Each round polynomial is univariate of degree ≤ d (constraint degree)
        round_polynomials: [][]F, // [num_vars][degree+1] coefficients

        /// Final evaluation point (random challenge point)
        final_point: []F, // [num_vars] coordinates

        /// Final evaluation value
        final_eval: F,

        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator, num_vars: usize, degree: usize) !Self {
            const round_polys = try allocator.alloc([]F, num_vars);
            errdefer allocator.free(round_polys);

            for (round_polys) |*poly| {
                poly.* = try allocator.alloc(F, degree + 1);
            }

            const final_point = try allocator.alloc(F, num_vars);

            return Self{
                .num_vars = num_vars,
                .round_polynomials = round_polys,
                .final_point = final_point,
                .final_eval = F.zero(),
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
    };
}

/// Lasso lookup proof component
pub fn LassoProof(comptime F: type) type {
    return struct {
        const Self = @This();

        /// Table identifier (which instruction table)
        table_id: u32,

        /// Number of lookups in this table
        num_lookups: usize,

        /// Multiset equality proof (sumcheck-based)
        /// Proves that the multiset of lookup queries equals
        /// a subset of the table entries
        multiset_proof: SumcheckProof(F),

        /// Decomposition proofs (for large tables split into chunks)
        subtable_proofs: ?[]SumcheckProof(F),

        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator, table_id: u32, num_lookups: usize, num_vars: usize) !Self {
            const multiset_proof = try SumcheckProof(F).init(allocator, num_vars, 2);

            return Self{
                .table_id = table_id,
                .num_lookups = num_lookups,
                .multiset_proof = multiset_proof,
                .subtable_proofs = null,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            self.multiset_proof.deinit();
            if (self.subtable_proofs) |proofs| {
                for (proofs) |*proof| {
                    proof.deinit();
                }
                self.allocator.free(proofs);
            }
        }
    };
}

/// Polynomial commitment opening
pub fn CommitmentOpening(comptime F: type) type {
    return struct {
        const Self = @This();

        /// Commitment (Merkle root)
        commitment: [32]u8,

        /// Evaluation point
        point: []F,

        /// Claimed evaluation value
        value: F,

        /// Opening proof (Merkle authentication path)
        proof: polynomial_commit.OpeningProof,

        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator, num_vars: usize) !Self {
            const point = try allocator.alloc(F, num_vars);
            const proof = try polynomial_commit.OpeningProof.init(allocator);

            return Self{
                .commitment = undefined,
                .point = point,
                .value = F.zero(),
                .proof = proof,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            self.allocator.free(self.point);
            self.proof.deinit();
        }
    };
}

/// Complete zkVM proof
pub fn Proof(comptime F: type) type {
    return struct {
        const Self = @This();

        /// Public inputs and outputs
        public_io: PublicIO,

        /// Main constraint satisfaction proof (sumcheck)
        /// Proves that all 43 witness polynomials satisfy:
        /// - PC progression constraints
        /// - Register update constraints
        /// - Memory consistency constraints
        constraint_proof: SumcheckProof(F),

        /// Lasso lookup proofs (one per instruction type used)
        lookup_proofs: std.ArrayList(LassoProof(F)),

        /// Polynomial commitments to witness polynomials
        /// Commits to the 43 multilinear polynomials:
        /// - 1 PC polynomial
        /// - 32 register polynomials
        /// - 7 instruction field polynomials
        /// - 3 memory access polynomials
        witness_commitments: []CommitmentOpening(F),

        /// Proof metadata
        metadata: ProofMetadata,

        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator, num_steps: usize) !Self {
            const num_vars = std.math.log2_int_ceil(usize, num_steps);

            // Initialize constraint proof (main sumcheck)
            var constraint_proof = try SumcheckProof(F).init(allocator, num_vars, 3);
            errdefer constraint_proof.deinit();

            // Initialize lookup proofs list
            var lookup_proofs = std.ArrayList(LassoProof(F)).init(allocator);
            errdefer {
                for (lookup_proofs.items) |*proof| {
                    proof.deinit();
                }
                lookup_proofs.deinit();
            }

            // Initialize witness commitments (43 polynomials)
            const witness_commitments = try allocator.alloc(CommitmentOpening(F), 43);
            errdefer allocator.free(witness_commitments);

            for (witness_commitments) |*opening| {
                opening.* = try CommitmentOpening(F).init(allocator, num_vars);
            }

            return Self{
                .public_io = undefined, // Set by prover
                .constraint_proof = constraint_proof,
                .lookup_proofs = lookup_proofs,
                .witness_commitments = witness_commitments,
                .metadata = ProofMetadata{
                    .num_steps = num_steps,
                    .num_vars = num_vars,
                    .field_modulus = F.MODULUS,
                    .version = 1,
                },
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            self.public_io.deinit(self.allocator);
            self.constraint_proof.deinit();

            for (self.lookup_proofs.items) |*proof| {
                proof.deinit();
            }
            self.lookup_proofs.deinit();

            for (self.witness_commitments) |*opening| {
                opening.deinit();
            }
            self.allocator.free(self.witness_commitments);
        }

        /// Estimate proof size in bytes
        pub fn estimateSize(self: Self) usize {
            var size: usize = 0;

            // Public IO (fixed size + variable register arrays)
            size += 32; // program_hash
            size += 8; // initial_pc
            size += 8; // final_pc
            size += 8; // num_steps
            if (self.public_io.initial_regs) |regs| {
                size += regs.len * 8;
            }
            if (self.public_io.final_regs) |regs| {
                size += regs.len * 8;
            }

            // Constraint proof: O(num_vars * degree * field_size)
            const field_size = @sizeOf(u64); // Field element size
            size += self.metadata.num_vars * 4 * field_size; // Degree-3 polynomials
            size += self.metadata.num_vars * field_size; // Final point
            size += field_size; // Final eval

            // Lookup proofs: O(num_tables * num_vars * field_size)
            for (self.lookup_proofs.items) |lasso| {
                size += 4; // table_id
                size += 8; // num_lookups
                size += lasso.multiset_proof.num_vars * 3 * field_size;
            }

            // Witness commitments: O(num_polys * log(n))
            size += self.witness_commitments.len * 32; // Merkle roots
            size += self.witness_commitments.len * 20 * 32; // Auth paths (approx)

            return size;
        }
    };
}

/// Proof metadata
pub const ProofMetadata = struct {
    /// Number of execution steps
    num_steps: usize,

    /// Number of variables in polynomials (log2(num_steps))
    num_vars: usize,

    /// Field modulus being used
    field_modulus: u64,

    /// Proof format version
    version: u32,
};

// ============================================================================
// Proof Verification Result
// ============================================================================

pub const VerificationResult = enum {
    Accept,
    RejectInvalidSumcheck,
    RejectInvalidLookup,
    RejectInvalidCommitment,
    RejectInvalidPublicIO,
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const BabyBear = @import("../core/field_presets.zig").BabyBear;

test "proof: initialization and cleanup" {
    const allocator = testing.allocator;

    var proof = try Proof(BabyBear).init(allocator, 16);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 16), proof.metadata.num_steps);
    try testing.expectEqual(@as(usize, 4), proof.metadata.num_vars); // log2(16) = 4
    try testing.expectEqual(@as(usize, 43), proof.witness_commitments.len);
}

test "proof: sumcheck proof structure" {
    const allocator = testing.allocator;

    var sumcheck_proof = try SumcheckProof(BabyBear).init(allocator, 5, 3);
    defer sumcheck_proof.deinit();

    try testing.expectEqual(@as(usize, 5), sumcheck_proof.num_vars);
    try testing.expectEqual(@as(usize, 5), sumcheck_proof.round_polynomials.len);

    // Each round polynomial has degree+1 coefficients
    for (sumcheck_proof.round_polynomials) |poly| {
        try testing.expectEqual(@as(usize, 4), poly.len); // degree 3 -> 4 coeffs
    }
}

test "proof: lasso proof structure" {
    const allocator = testing.allocator;

    var lasso_proof = try LassoProof(BabyBear).init(allocator, 42, 100, 4);
    defer lasso_proof.deinit();

    try testing.expectEqual(@as(u32, 42), lasso_proof.table_id);
    try testing.expectEqual(@as(usize, 100), lasso_proof.num_lookups);
}

test "proof: size estimation" {
    const allocator = testing.allocator;

    var proof = try Proof(BabyBear).init(allocator, 1024);
    defer proof.deinit();

    const estimated_size = proof.estimateSize();

    // Should be roughly O(log n) in steps
    // For 1024 steps (10 variables), expect ~10-50 KB
    try testing.expect(estimated_size > 1000); // At least 1 KB
    try testing.expect(estimated_size < 100_000); // Less than 100 KB
}
