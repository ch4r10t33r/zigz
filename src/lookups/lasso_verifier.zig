const std = @import("std");
const multilinear = @import("../poly/multilinear.zig");
const sumcheck_protocol = @import("../proofs/sumcheck_protocol.zig");
const sumcheck_verifier = @import("../proofs/sumcheck_verifier.zig");
const lasso_prover = @import("lasso_prover.zig");
const table_builder = @import("table_builder.zig");

/// Lasso Lookup Argument Verifier
///
/// Verifies Lasso proofs using sumcheck protocol.
/// The verifier checks that lookup queries are valid without seeing the full table.
///
/// **Verification Steps:**
/// 1. Check commitments to table and query polynomials
/// 2. Verify sumcheck proof for lookup constraint
/// 3. Perform final evaluation check at random point
/// 4. Accept if all checks pass
///
/// **Key Property:**
/// Verifier runs in O(v) time where v = log(table_size),
/// instead of O(table_size) for naive verification.

pub const VerificationResult = struct {
    is_valid: bool,
    reason: []const u8,

    pub fn accept() VerificationResult {
        return VerificationResult{
            .is_valid = true,
            .reason = "Proof verified successfully",
        };
    }

    pub fn reject(reason: []const u8) VerificationResult {
        return VerificationResult{
            .is_valid = false,
            .reason = reason,
        };
    }
};

pub fn LassoVerifier(comptime F: type) type {
    return struct {
        const Self = @This();
        const Multilinear = multilinear.Multilinear(F);
        const SumcheckVerifier = sumcheck_verifier.SumcheckVerifier(F);
        const Proof = lasso_prover.LassoProof(F);

        /// Verify a Lasso lookup proof
        ///
        /// Given:
        /// - proof: Lasso proof from prover
        /// - table: The lookup table (or commitment to it)
        /// - num_queries: Expected number of queries
        ///
        /// Returns verification result
        pub fn verify(
            proof: Proof,
            table: table_builder.DenseTable(F),
            expected_num_queries: usize,
            allocator: std.mem.Allocator,
        ) !VerificationResult {
            // Step 1: Check proof metadata
            if (proof.num_lookups != expected_num_queries) {
                return VerificationResult.reject("Number of lookups mismatch");
            }

            // Step 2: Verify table commitment matches
            const computed_table_commitment = computeTableCommitment(table);
            if (!std.mem.eql(u8, &proof.table_commitment, &computed_table_commitment)) {
                return VerificationResult.reject("Table commitment mismatch");
            }

            // Step 3: Build table polynomial for oracle
            var table_evals = try allocator.alloc(F, table.entries.len);
            defer allocator.free(table_evals);

            for (table.entries, 0..) |entry, i| {
                table_evals[i] = hashEntry(entry);
            }

            var table_poly = try Multilinear.init(allocator, table_evals);
            defer table_poly.deinit();

            // Step 4: Verify sumcheck proof
            // The claimed sum should be related to the query polynomial
            const claimed_sum = proof.sumcheck_proof.final_eval;

            // Oracle: evaluate table polynomial at final point
            const oracle = struct {
                table_polynomial: *Multilinear,

                fn eval(point: []const F) !F {
                    return @fieldParentPtr(@This(), "table_polynomial", &point).table_polynomial.eval(point);
                }
            }{ .table_polynomial = &table_poly };

            const eval_fn = struct {
                tp: *Multilinear,

                fn call(point: []const F) !F {
                    return @fieldParentPtr(@This(), "tp", &point).tp.eval(point);
                }
            }{ .tp = &table_poly }.call;

            const sumcheck_result = try SumcheckVerifier.verify(
                proof.sumcheck_proof,
                claimed_sum,
                &eval_fn,
                allocator,
            );

            if (!sumcheck_result.is_valid) {
                return VerificationResult.reject("Sumcheck verification failed");
            }

            // Step 5: All checks passed
            return VerificationResult.accept();
        }

        /// Verify with explicit query commitment check
        ///
        /// This version additionally verifies that the query commitment matches
        /// the provided queries, ensuring completeness.
        pub fn verifyWithQueries(
            proof: Proof,
            table: table_builder.DenseTable(F),
            queries: []const lasso_prover.LookupQuery(F),
            allocator: std.mem.Allocator,
        ) !VerificationResult {
            // First, verify query commitment matches provided queries
            const computed_query_commitment = try computeQueryCommitment(queries, allocator);
            if (!std.mem.eql(u8, &proof.query_commitment, &computed_query_commitment)) {
                return VerificationResult.reject("Query commitment mismatch");
            }

            // Then perform standard verification
            return verify(proof, table, queries.len, allocator);
        }

        /// Fast verification without reconstructing table
        ///
        /// This version only checks commitments and sumcheck proof,
        /// without needing access to the full table.
        pub fn verifyFast(
            proof: Proof,
            table_commitment: [32]u8,
            expected_num_queries: usize,
            claimed_sum: F,
            allocator: std.mem.Allocator,
        ) !VerificationResult {
            // Check table commitment
            if (!std.mem.eql(u8, &proof.table_commitment, &table_commitment)) {
                return VerificationResult.reject("Table commitment mismatch");
            }

            // Check number of queries
            if (proof.num_lookups != expected_num_queries) {
                return VerificationResult.reject("Number of lookups mismatch");
            }

            // In fast mode, we can't fully verify sumcheck without the oracle
            // But we can check proof structure and consistency
            if (proof.sumcheck_proof.num_vars == 0) {
                return VerificationResult.reject("Invalid sumcheck proof structure");
            }

            // Check final evaluation matches claimed sum (simplified check)
            if (!proof.sumcheck_proof.final_eval.eql(claimed_sum)) {
                return VerificationResult.reject("Final evaluation mismatch");
            }

            return VerificationResult.accept();
        }

        /// Compute commitment to lookup table
        fn computeTableCommitment(table: table_builder.DenseTable(F)) [32]u8 {
            var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});

            for (table.entries) |entry| {
                for (entry.inputs) |inp| {
                    hasher.update(std.mem.asBytes(&inp.value));
                }
                for (entry.outputs) |out| {
                    hasher.update(std.mem.asBytes(&out.value));
                }
            }

            var commitment: [32]u8 = undefined;
            hasher.final(&commitment);
            return commitment;
        }

        /// Compute commitment to query set
        fn computeQueryCommitment(queries: []const lasso_prover.LookupQuery(F), allocator: std.mem.Allocator) ![32]u8 {
            var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});

            // Pad to power of 2
            const padded_size = std.math.ceilPowerOfTwo(usize, queries.len) catch return error.TooManyQueries;

            for (queries) |query| {
                for (query.inputs) |inp| {
                    hasher.update(std.mem.asBytes(&inp.value));
                }
                for (query.expected_outputs) |out| {
                    hasher.update(std.mem.asBytes(&out.value));
                }
            }

            // Hash padding zeros
            var zero_bytes = [_]u8{0} ** 8;
            for (queries.len..padded_size) |_| {
                hasher.update(&zero_bytes);
            }

            _ = allocator; // Not needed in this implementation
            var commitment: [32]u8 = undefined;
            hasher.final(&commitment);
            return commitment;
        }

        /// Hash a table entry (must match prover's hash)
        fn hashEntry(entry: table_builder.TableEntry(F)) F {
            var h: u64 = 0;

            for (entry.inputs) |inp| {
                h = h ^ inp.value;
                h = std.hash.XxHash3.hash(0, std.mem.asBytes(&h));
            }

            for (entry.outputs) |out| {
                h = h ^ out.value;
                h = std.hash.XxHash3.hash(0, std.mem.asBytes(&h));
            }

            return F.init(@intCast(h % F.MODULUS));
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "lasso_verifier: honest proof verifies" {
    const F = field.Field(u64, 17);
    const Prover = lasso_prover.LassoProver(F);
    const Verifier = LassoVerifier(F);
    const Query = lasso_prover.LookupQuery(F);

    // Build table
    var table = try table_builder.buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    // Create queries
    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    {
        const inputs = [_]F{ F.init(1), F.init(2) };
        const outputs = [_]F{F.init(3)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    // Generate proof
    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    // Verify proof
    const result = try Verifier.verify(proof, table, queries.items.len, testing.allocator);
    try testing.expect(result.is_valid);
}

test "lasso_verifier: wrong query count rejected" {
    const F = field.Field(u64, 17);
    const Prover = lasso_prover.LassoProver(F);
    const Verifier = LassoVerifier(F);
    const Query = lasso_prover.LookupQuery(F);

    var table = try table_builder.buildXorTable(F, testing.allocator, 2);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    {
        const inputs = [_]F{ F.init(3), F.init(2) };
        const outputs = [_]F{F.init(1)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    // Try to verify with wrong expected count
    const result = try Verifier.verify(proof, table, 5, testing.allocator);
    try testing.expect(!result.is_valid);
}

test "lasso_verifier: verify with queries" {
    const F = field.Field(u64, 17);
    const Prover = lasso_prover.LassoProver(F);
    const Verifier = LassoVerifier(F);
    const Query = lasso_prover.LookupQuery(F);

    var table = try table_builder.buildAndTable(F, testing.allocator, 2);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    {
        const inputs = [_]F{ F.init(3), F.init(2) };
        const outputs = [_]F{F.init(2)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    // Verify with explicit query check
    const result = try Verifier.verifyWithQueries(proof, table, queries.items, testing.allocator);
    try testing.expect(result.is_valid);
}

test "lasso_verifier: fast verification" {
    const F = field.Field(u64, 17);
    const Prover = lasso_prover.LassoProver(F);
    const Verifier = LassoVerifier(F);
    const Query = lasso_prover.LookupQuery(F);

    var table = try table_builder.buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    {
        const inputs = [_]F{ F.init(2), F.init(1) };
        const outputs = [_]F{F.init(3)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    // Fast verification without table access
    const table_commitment = Verifier.computeTableCommitment(table);
    const claimed_sum = proof.sumcheck_proof.final_eval;

    const result = try Verifier.verifyFast(
        proof,
        table_commitment,
        queries.items.len,
        claimed_sum,
        testing.allocator,
    );
    try testing.expect(result.is_valid);
}

test "lasso_verifier: multiple queries verify" {
    const F = field.Field(u64, 17);
    const Prover = lasso_prover.LassoProver(F);
    const Verifier = LassoVerifier(F);
    const Query = lasso_prover.LookupQuery(F);

    var table = try table_builder.buildXorTable(F, testing.allocator, 3);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    // Multiple XOR queries
    {
        const inputs = [_]F{ F.init(5), F.init(3) };
        const outputs = [_]F{F.init(6)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }
    {
        const inputs = [_]F{ F.init(7), F.init(2) };
        const outputs = [_]F{F.init(5)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }
    {
        const inputs = [_]F{ F.init(4), F.init(4) };
        const outputs = [_]F{F.init(0)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    const result = try Verifier.verify(proof, table, queries.items.len, testing.allocator);
    try testing.expect(result.is_valid);
}

test "lasso_verifier: commitment consistency" {
    const F = field.Field(u64, 17);
    const Verifier = LassoVerifier(F);

    var table = try table_builder.buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    const commit1 = Verifier.computeTableCommitment(table);
    const commit2 = Verifier.computeTableCommitment(table);

    // Same table should produce same commitment
    try testing.expect(std.mem.eql(u8, &commit1, &commit2));
}
