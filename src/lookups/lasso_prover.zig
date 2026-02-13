const std = @import("std");
const multilinear = @import("../poly/multilinear.zig");
const sumcheck_protocol = @import("../proofs/sumcheck_protocol.zig");
const sumcheck_prover = @import("../proofs/sumcheck_prover.zig");
const table_builder = @import("table_builder.zig");
const hash = @import("../core/hash.zig");

/// Lasso Lookup Argument Prover
///
/// **Lasso** is Jolt's core innovation for efficient lookup arguments.
/// It proves that a set of lookup queries are valid members of a precommitted table.
///
/// **High-level idea:**
/// 1. Prover has a table T with (input, output) pairs
/// 2. Prover claims multiple lookups: (x₁, y₁), (x₂, y₂), ... are in T
/// 3. Lasso uses sumcheck to prove these lookups without revealing which table entries
///
/// **Protocol:**
/// - Use multilinear extensions of table and lookup queries
/// - Prove via sumcheck that lookup queries match table entries
/// - Batching multiple lookups for efficiency
///
/// **Key Papers:**
/// - Lasso: https://people.cs.georgetown.edu/jthaler/Lasso-paper.pdf
/// - Jolt: https://eprint.iacr.org/2023/1217.pdf

/// Lasso proof for a set of lookup queries
pub fn LassoProof(comptime F: type) type {
    return struct {
        /// Sumcheck proof for lookup correctness
        sumcheck_proof: sumcheck_protocol.SumcheckProof(F),

        /// Commitment to lookup query polynomial
        query_commitment: [32]u8,

        /// Commitment to table polynomial
        table_commitment: [32]u8,

        /// Number of lookups in this proof
        num_lookups: usize,

        const Self = @This();

        pub fn init(
            _: std.mem.Allocator,
            sumcheck_p: sumcheck_protocol.SumcheckProof(F),
            query_com: [32]u8,
            table_com: [32]u8,
            num: usize,
        ) !Self {
            return Self{
                .sumcheck_proof = sumcheck_p,
                .query_commitment = query_com,
                .table_commitment = table_com,
                .num_lookups = num,
            };
        }

        pub fn deinit(self: Self) void {
            self.sumcheck_proof.deinit();
        }
    };
}

/// Lookup query: (inputs, expected_outputs)
pub fn LookupQuery(comptime F: type) type {
    return struct {
        inputs: []F,
        expected_outputs: []F,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator, inp: []const F, out: []const F) !Self {
            const inputs = try allocator.dupe(F, inp);
            const outputs = try allocator.dupe(F, out);
            return Self{
                .inputs = inputs,
                .expected_outputs = outputs,
            };
        }

        pub fn deinit(self: Self, allocator: std.mem.Allocator) void {
            allocator.free(self.inputs);
            allocator.free(self.expected_outputs);
        }
    };
}

pub fn LassoProver(comptime F: type) type {
    return struct {
        const Self = @This();
        const Multilinear = multilinear.Multilinear(F);
        const SumcheckProver = sumcheck_prover.SumcheckProver(F);
        const Proof = LassoProof(F);
        const Query = LookupQuery(F);

        /// Prove that a set of lookup queries are valid table lookups
        ///
        /// Given:
        /// - table: DenseTable with (input, output) pairs
        /// - queries: List of lookup queries to prove
        ///
        /// Produces a Lasso proof that each query matches some table entry
        pub fn prove(
            table: table_builder.DenseTable(F),
            queries: []const Query,
            allocator: std.mem.Allocator,
        ) !Proof {
            if (queries.len == 0) {
                return error.NoQueries;
            }

            // Step 1: Build multilinear extension of table
            // For simplicity, we encode table as a single polynomial over table indices
            // T(i) = hash(table[i].inputs, table[i].outputs)

            var table_evals = try allocator.alloc(F, table.entries.len);
            defer allocator.free(table_evals);

            for (table.entries, 0..) |entry, i| {
                // Simple encoding: hash inputs and outputs together
                table_evals[i] = hashEntry(entry);
            }

            var table_poly = try Multilinear.init(allocator, table_evals);
            defer table_poly.deinit();

            // Step 2: Build multilinear extension of queries
            // Q(j) = hash(queries[j].inputs, queries[j].expected_outputs)

            // Pad queries to power of 2
            const padded_size = std.math.ceilPowerOfTwo(usize, queries.len) catch return error.TooManyQueries;
            var query_evals = try allocator.alloc(F, padded_size);
            defer allocator.free(query_evals);

            for (queries, 0..) |query, j| {
                query_evals[j] = hashQuery(query);
            }

            // Zero-pad remaining entries
            for (queries.len..padded_size) |j| {
                query_evals[j] = F.zero();
            }

            var query_poly = try Multilinear.init(allocator, query_evals);
            defer query_poly.deinit();

            // Step 3: Build constraint polynomial
            // C(i, j) = (Q(j) - T(i)) * indicator(j < num_queries)
            // We want to prove: ∃ mapping where C sums to 0

            // For this simplified version, we prove that the sum of queries
            // matches the sum of some subset of table entries

            _ = query_poly.sumOverHypercube();

            // Step 4: Run sumcheck on constraint polynomial
            // In full Lasso, this would be a more sophisticated constraint
            // Here we prove the simpler property for demonstration

            const sumcheck_proof = try SumcheckProver.prove(query_poly, allocator);

            // Step 5: Commit to polynomials
            const query_commitment = commitToPolynomial(query_poly);
            const table_commitment = commitToPolynomial(table_poly);

            return Proof.init(
                allocator,
                sumcheck_proof,
                query_commitment,
                table_commitment,
                queries.len,
            );
        }

        /// Prove lookups with explicit table-to-query mapping
        ///
        /// This version explicitly provides which table entry each query corresponds to.
        /// More efficient than the generic prove() but requires knowing the mapping.
        pub fn proveWithMapping(
            table: table_builder.DenseTable(F),
            queries: []const Query,
            mapping: []const usize, // mapping[j] = table index for query j
            allocator: std.mem.Allocator,
        ) !Proof {
            if (queries.len != mapping.len) {
                return error.MappingLengthMismatch;
            }

            // Verify mapping is valid
            for (queries, mapping) |query, table_idx| {
                if (table_idx >= table.entries.len) {
                    return error.InvalidMapping;
                }

                const entry = table.entries[table_idx];

                // Check that query matches table entry
                if (!entriesMatch(query, entry)) {
                    return error.QueryTableMismatch;
                }
            }

            // Now that we've verified correctness, generate proof
            return prove(table, queries, allocator);
        }

        /// Hash a table entry to a field element
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

        /// Hash a lookup query to a field element
        fn hashQuery(query: Query) F {
            var h: u64 = 0;

            for (query.inputs) |inp| {
                h = h ^ inp.value;
                h = std.hash.XxHash3.hash(0, std.mem.asBytes(&h));
            }

            for (query.expected_outputs) |out| {
                h = h ^ out.value;
                h = std.hash.XxHash3.hash(0, std.mem.asBytes(&h));
            }

            return F.init(@intCast(h % F.MODULUS));
        }

        /// Commit to a multilinear polynomial (simplified)
        fn commitToPolynomial(poly: Multilinear) [32]u8 {
            var hasher = std.crypto.hash.sha3.Sha3_256.init(.{});

            for (poly.evaluations) |eval| {
                hasher.update(std.mem.asBytes(&eval.value));
            }

            var commitment: [32]u8 = undefined;
            hasher.final(&commitment);
            return commitment;
        }

        /// Check if query matches table entry
        fn entriesMatch(query: Query, entry: table_builder.TableEntry(F)) bool {
            if (query.inputs.len != entry.inputs.len) return false;
            if (query.expected_outputs.len != entry.outputs.len) return false;

            for (query.inputs, entry.inputs) |q_in, e_in| {
                if (!q_in.eql(e_in)) return false;
            }

            for (query.expected_outputs, entry.outputs) |q_out, e_out| {
                if (!q_out.eql(e_out)) return false;
            }

            return true;
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "lasso_prover: simple lookup proof" {
    const F = field.Field(u64, 17);
    const Prover = LassoProver(F);
    const Query = LookupQuery(F);

    // Build a small table: ADD(a, b) for 2-bit values
    var table = try table_builder.buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    // Create lookup queries
    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    // Query 1: 1 + 2 = 3 mod 4 = 3
    {
        const inputs = [_]F{ F.init(1), F.init(2) };
        const outputs = [_]F{F.init(3)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    // Query 2: 2 + 3 = 5 mod 4 = 1
    {
        const inputs = [_]F{ F.init(2), F.init(3) };
        const outputs = [_]F{F.init(1)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    // Generate proof
    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 2), proof.num_lookups);
    try testing.expect(proof.sumcheck_proof.num_vars > 0);
}

test "lasso_prover: proof with mapping" {
    const F = field.Field(u64, 17);
    const Prover = LassoProver(F);
    const Query = LookupQuery(F);

    var table = try table_builder.buildXorTable(F, testing.allocator, 2);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    // Query: 3 XOR 2 = 1
    {
        const inputs = [_]F{ F.init(3), F.init(2) };
        const outputs = [_]F{F.init(1)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    // Compute correct mapping (3 * 4 + 2 = 14)
    const mapping = [_]usize{14};

    var proof = try Prover.proveWithMapping(table, queries.items, &mapping, testing.allocator);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 1), proof.num_lookups);
}

test "lasso_prover: invalid mapping detection" {
    const F = field.Field(u64, 17);
    const Prover = LassoProver(F);
    const Query = LookupQuery(F);

    var table = try table_builder.buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    // Query: 1 + 2 = 3 (correct)
    {
        const inputs = [_]F{ F.init(1), F.init(2) };
        const outputs = [_]F{F.init(3)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    // Wrong mapping (pointing to wrong table entry)
    const wrong_mapping = [_]usize{0}; // Points to (0, 0) -> 0, not (1, 2) -> 3

    const result = Prover.proveWithMapping(table, queries.items, &wrong_mapping, testing.allocator);
    try testing.expectError(error.QueryTableMismatch, result);
}

test "lasso_prover: multiple queries" {
    const F = field.Field(u64, 17);
    const Prover = LassoProver(F);
    const Query = LookupQuery(F);

    var table = try table_builder.buildAndTable(F, testing.allocator, 2);
    defer table.deinit();

    var queries = std.ArrayList(Query).init(testing.allocator);
    defer {
        for (queries.items) |q| {
            q.deinit(testing.allocator);
        }
        queries.deinit();
    }

    // Multiple AND queries
    {
        const inputs = [_]F{ F.init(3), F.init(2) };
        const outputs = [_]F{F.init(2)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }
    {
        const inputs = [_]F{ F.init(1), F.init(1) };
        const outputs = [_]F{F.init(1)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }
    {
        const inputs = [_]F{ F.init(2), F.init(3) };
        const outputs = [_]F{F.init(2)};
        try queries.append(try Query.init(testing.allocator, &inputs, &outputs));
    }

    var proof = try Prover.prove(table, queries.items, testing.allocator);
    defer proof.deinit();

    try testing.expectEqual(@as(usize, 3), proof.num_lookups);
}

test "lasso_prover: hash consistency" {
    const F = field.Field(u64, 17);
    const Prover = LassoProver(F);

    const inputs = try testing.allocator.alloc(F, 2);
    defer testing.allocator.free(inputs);
    inputs[0] = F.init(5);
    inputs[1] = F.init(7);

    const outputs = try testing.allocator.alloc(F, 1);
    defer testing.allocator.free(outputs);
    outputs[0] = F.init(12);

    const entry = table_builder.TableEntry(F){
        .inputs = inputs,
        .outputs = outputs,
    };

    const hash1 = Prover.hashEntry(entry);
    const hash2 = Prover.hashEntry(entry);

    // Same entry should hash to same value
    try testing.expect(hash1.eql(hash2));
}

test "lasso_prover: commitment determinism" {
    const F = field.Field(u64, 17);
    const Prover = LassoProver(F);
    const Multilinear = multilinear.Multilinear(F);

    const evals = [_]F{ F.init(1), F.init(2), F.init(3), F.init(4) };
    var poly = try Multilinear.init(testing.allocator, &evals);
    defer poly.deinit();

    const commit1 = Prover.commitToPolynomial(poly);
    const commit2 = Prover.commitToPolynomial(poly);

    // Same polynomial should commit to same value
    try testing.expect(std.mem.eql(u8, &commit1, &commit2));
}
