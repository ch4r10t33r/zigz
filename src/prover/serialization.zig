const std = @import("std");
const field = @import("../core/field.zig");
const proof_mod = @import("proof.zig");

/// Proof Serialization for zigz zkVM
///
/// Provides binary and JSON serialization for proofs.
/// Binary format is compact and efficient for storage/network transmission.
/// JSON format is human-readable for debugging and verification.
///
/// Binary Format Structure:
/// ```
/// [Header: 32 bytes]
/// - Magic number: "ZIGZ" (4 bytes)
/// - Version: u32 (4 bytes)
/// - Field modulus: u64 (8 bytes)
/// - Num steps: u64 (8 bytes)
/// - Num vars: u32 (4 bytes)
/// - Reserved: 4 bytes
///
/// [Public IO: variable]
/// - Program hash: 32 bytes
/// - Initial PC: u64 (8 bytes)
/// - Final PC: u64 (8 bytes)
/// - Num initial regs: u32 (4 bytes)
/// - Initial regs: [u64; n]
/// - Num final regs: u32 (4 bytes)
/// - Final regs: [u64; n]
///
/// [Constraint Proof: variable]
/// - Round polynomials: [num_vars][degree+1]F
/// - Final point: [num_vars]F
/// - Final eval: F
///
/// [Lasso Proofs: variable]
/// - Num proofs: u32 (4 bytes)
/// - For each proof:
///   - Table ID: u32
///   - Num lookups: u64
///   - Multiset proof data
///
/// [Witness Commitments: variable]
/// - For each of 43 polynomials:
///   - Commitment: 32 bytes
///   - Evaluation point: [num_vars]F
///   - Value: F
///   - Opening proof data
/// ```

const MAGIC_NUMBER: [4]u8 = "ZIGZ".*;
const CURRENT_VERSION: u32 = 1;

/// Serialization error types
pub const SerializationError = error{
    InvalidMagicNumber,
    UnsupportedVersion,
    FieldMismatch,
    BufferTooSmall,
    InvalidData,
};

/// Binary serializer for proofs
pub fn BinarySerializer(comptime F: type) type {
    return struct {
        const Self = @This();
        const Proof = proof_mod.Proof(F);

        /// Serialize a proof to bytes
        pub fn serialize(allocator: std.mem.Allocator, proof: Proof) ![]u8 {
            // Estimate total size
            const estimated_size = estimateSize(proof);
            var buffer = try allocator.alloc(u8, estimated_size);
            errdefer allocator.free(buffer);

            var stream = std.io.fixedBufferStream(buffer);
            var writer = stream.writer();

            // Write header
            try writeHeader(&writer, proof);

            // Write public IO
            try writePublicIO(&writer, proof.public_io);

            // Write constraint proof
            try writeConstraintProof(&writer, proof.constraint_proof);

            // Write Lasso proofs
            try writeLassoProofs(&writer, proof.lookup_proofs.items);

            // Write witness commitments
            try writeWitnessCommitments(&writer, proof.witness_commitments);

            // Trim to actual size
            const actual_size = stream.pos;
            return allocator.realloc(buffer, actual_size);
        }

        /// Deserialize a proof from bytes
        pub fn deserialize(allocator: std.mem.Allocator, data: []const u8) !Proof {
            var stream = std.io.fixedBufferStream(data);
            var reader = stream.reader();

            // Read and validate header
            const metadata = try readHeader(&reader);

            // Verify field matches
            if (metadata.field_modulus != F.MODULUS) {
                return SerializationError.FieldMismatch;
            }

            // Initialize proof structure
            var proof = try Proof.init(allocator, metadata.num_steps);
            errdefer proof.deinit();

            proof.metadata = metadata;

            // Read public IO
            proof.public_io = try readPublicIO(allocator, &reader);
            errdefer proof.public_io.deinit(allocator);

            // Read constraint proof
            try readConstraintProof(&reader, &proof.constraint_proof);

            // Read Lasso proofs
            try readLassoProofs(allocator, &reader, &proof.lookup_proofs);

            // Read witness commitments
            try readWitnessCommitments(&reader, proof.witness_commitments);

            return proof;
        }

        /// Estimate serialized size
        fn estimateSize(proof: Proof) usize {
            var size: usize = 0;

            // Header
            size += 32;

            // Public IO
            size += 32 + 8 + 8 + 4 + 4; // Fixed fields
            if (proof.public_io.initial_regs) |regs| {
                size += regs.len * 8;
            }
            if (proof.public_io.final_regs) |regs| {
                size += regs.len * 8;
            }

            // Constraint proof
            const field_size = 8; // u64 field elements
            size += proof.metadata.num_vars * 4 * field_size; // Round polynomials
            size += proof.metadata.num_vars * field_size; // Final point
            size += field_size; // Final eval

            // Lasso proofs
            size += 4; // Num proofs
            for (proof.lookup_proofs.items) |lasso| {
                size += 4 + 8; // Table ID + num lookups
                size += lasso.multiset_proof.num_vars * 3 * field_size;
                size += lasso.multiset_proof.num_vars * field_size;
                size += field_size;
            }

            // Witness commitments
            for (proof.witness_commitments) |commitment| {
                size += 32; // Commitment hash
                size += commitment.point.len * field_size;
                size += field_size; // Value
                size += 32 * 20; // Opening proof (estimate)
            }

            return size;
        }

        fn writeHeader(writer: anytype, proof: Proof) !void {
            try writer.writeAll(&MAGIC_NUMBER);
            try writer.writeInt(u32, CURRENT_VERSION, .little);
            try writer.writeInt(u64, proof.metadata.field_modulus, .little);
            try writer.writeInt(u64, @intCast(proof.metadata.num_steps), .little);
            try writer.writeInt(u32, @intCast(proof.metadata.num_vars), .little);
            try writer.writeInt(u32, 0, .little); // Reserved
        }

        fn readHeader(reader: anytype) !proof_mod.ProofMetadata {
            var magic: [4]u8 = undefined;
            _ = try reader.readAll(&magic);
            if (!std.mem.eql(u8, &magic, &MAGIC_NUMBER)) {
                return SerializationError.InvalidMagicNumber;
            }

            const version = try reader.readInt(u32, .little);
            if (version != CURRENT_VERSION) {
                return SerializationError.UnsupportedVersion;
            }

            const field_modulus = try reader.readInt(u64, .little);
            const num_steps = try reader.readInt(u64, .little);
            const num_vars = try reader.readInt(u32, .little);
            _ = try reader.readInt(u32, .little); // Reserved

            return proof_mod.ProofMetadata{
                .num_steps = @intCast(num_steps),
                .num_vars = @intCast(num_vars),
                .field_modulus = field_modulus,
                .version = version,
            };
        }

        fn writePublicIO(writer: anytype, public_io: proof_mod.PublicIO) !void {
            try writer.writeAll(&public_io.program_hash);
            try writer.writeInt(u64, public_io.initial_pc, .little);
            try writer.writeInt(u64, public_io.final_pc, .little);

            // Initial registers
            if (public_io.initial_regs) |regs| {
                try writer.writeInt(u32, @intCast(regs.len), .little);
                for (regs) |reg| {
                    try writer.writeInt(u64, reg, .little);
                }
            } else {
                try writer.writeInt(u32, 0, .little);
            }

            // Final registers
            if (public_io.final_regs) |regs| {
                try writer.writeInt(u32, @intCast(regs.len), .little);
                for (regs) |reg| {
                    try writer.writeInt(u64, reg, .little);
                }
            } else {
                try writer.writeInt(u32, 0, .little);
            }

            try writer.writeInt(u64, @intCast(public_io.num_steps), .little);
        }

        fn readPublicIO(allocator: std.mem.Allocator, reader: anytype) !proof_mod.PublicIO {
            var public_io: proof_mod.PublicIO = undefined;

            _ = try reader.readAll(&public_io.program_hash);
            public_io.initial_pc = try reader.readInt(u64, .little);
            public_io.final_pc = try reader.readInt(u64, .little);

            // Initial registers
            const num_initial_regs = try reader.readInt(u32, .little);
            if (num_initial_regs > 0) {
                const regs = try allocator.alloc(u64, num_initial_regs);
                for (regs) |*reg| {
                    reg.* = try reader.readInt(u64, .little);
                }
                public_io.initial_regs = regs;
            } else {
                public_io.initial_regs = null;
            }

            // Final registers
            const num_final_regs = try reader.readInt(u32, .little);
            if (num_final_regs > 0) {
                const regs = try allocator.alloc(u64, num_final_regs);
                for (regs) |*reg| {
                    reg.* = try reader.readInt(u64, .little);
                }
                public_io.final_regs = regs;
            } else {
                public_io.final_regs = null;
            }

            public_io.num_steps = @intCast(try reader.readInt(u64, .little));
            public_io.initial_memory = null;

            return public_io;
        }

        fn writeConstraintProof(writer: anytype, sumcheck: proof_mod.SumcheckProof(F)) !void {
            // Write round polynomials
            for (sumcheck.round_polynomials) |poly| {
                for (poly) |coeff| {
                    try writer.writeInt(u64, coeff.value, .little);
                }
            }

            // Write final point
            for (sumcheck.final_point) |coord| {
                try writer.writeInt(u64, coord.value, .little);
            }

            // Write final eval
            try writer.writeInt(u64, sumcheck.final_eval.value, .little);
        }

        fn readConstraintProof(reader: anytype, sumcheck: *proof_mod.SumcheckProof(F)) !void {
            // Read round polynomials
            for (sumcheck.round_polynomials) |poly| {
                for (poly) |*coeff| {
                    const value = try reader.readInt(u64, .little);
                    coeff.* = F.init(value);
                }
            }

            // Read final point
            for (sumcheck.final_point) |*coord| {
                const value = try reader.readInt(u64, .little);
                coord.* = F.init(value);
            }

            // Read final eval
            const eval_value = try reader.readInt(u64, .little);
            sumcheck.final_eval = F.init(eval_value);
        }

        fn writeLassoProofs(writer: anytype, proofs: []const proof_mod.LassoProof(F)) !void {
            try writer.writeInt(u32, @intCast(proofs.len), .little);

            for (proofs) |lasso| {
                try writer.writeInt(u32, lasso.table_id, .little);
                try writer.writeInt(u64, @intCast(lasso.num_lookups), .little);

                // Write multiset proof
                try writeConstraintProof(writer, lasso.multiset_proof);
            }
        }

        fn readLassoProofs(
            allocator: std.mem.Allocator,
            reader: anytype,
            proofs: *std.ArrayList(proof_mod.LassoProof(F)),
        ) !void {
            const num_proofs = try reader.readInt(u32, .little);

            for (0..num_proofs) |_| {
                const table_id = try reader.readInt(u32, .little);
                const num_lookups = try reader.readInt(u64, .little);

                // Create Lasso proof
                var lasso = try proof_mod.LassoProof(F).init(
                    allocator,
                    table_id,
                    @intCast(num_lookups),
                    4, // Default num_vars
                );
                errdefer lasso.deinit();

                // Read multiset proof
                try readConstraintProof(reader, &lasso.multiset_proof);

                try proofs.append(lasso);
            }
        }

        fn writeWitnessCommitments(writer: anytype, commitments: []const proof_mod.CommitmentOpening(F)) !void {
            for (commitments) |commitment| {
                try writer.writeAll(&commitment.commitment);

                for (commitment.point) |coord| {
                    try writer.writeInt(u64, coord.value, .little);
                }

                try writer.writeInt(u64, commitment.value.value, .little);

                // Write opening proof (placeholder)
                // TODO: Serialize actual Merkle authentication paths
            }
        }

        fn readWitnessCommitments(reader: anytype, commitments: []proof_mod.CommitmentOpening(F)) !void {
            for (commitments) |*commitment| {
                _ = try reader.readAll(&commitment.commitment);

                for (commitment.point) |*coord| {
                    const value = try reader.readInt(u64, .little);
                    coord.* = F.init(value);
                }

                const eval_value = try reader.readInt(u64, .little);
                commitment.value = F.init(eval_value);

                // Read opening proof (placeholder)
                // TODO: Deserialize actual Merkle authentication paths
            }
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const BabyBear = @import("../core/field_presets.zig").BabyBear;

test "serialization: round-trip binary" {
    const allocator = testing.allocator;

    // Create a simple proof
    var proof = try proof_mod.Proof(BabyBear).init(allocator, 16);
    defer proof.deinit();

    // Set some dummy data
    proof.public_io.program_hash = [_]u8{0x42} ** 32;
    proof.public_io.initial_pc = 0x1000;
    proof.public_io.final_pc = 0x1010;
    proof.public_io.num_steps = 16;

    // Serialize
    const serializer = BinarySerializer(BabyBear);
    const data = try serializer.serialize(allocator, proof);
    defer allocator.free(data);

    // Deserialize
    var deserialized = try serializer.deserialize(allocator, data);
    defer deserialized.deinit();

    // Verify
    try testing.expectEqual(proof.public_io.initial_pc, deserialized.public_io.initial_pc);
    try testing.expectEqual(proof.public_io.final_pc, deserialized.public_io.final_pc);
    try testing.expectEqual(proof.public_io.num_steps, deserialized.public_io.num_steps);
    try testing.expectEqualSlices(u8, &proof.public_io.program_hash, &deserialized.public_io.program_hash);
}

test "serialization: size estimation" {
    const allocator = testing.allocator;

    var proof = try proof_mod.Proof(BabyBear).init(allocator, 1024);
    defer proof.deinit();

    const serializer = BinarySerializer(BabyBear);
    const data = try serializer.serialize(allocator, proof);
    defer allocator.free(data);

    // Proof should be compact
    try testing.expect(data.len > 100); // At least 100 bytes
    try testing.expect(data.len < 1_000_000); // Less than 1 MB
}
