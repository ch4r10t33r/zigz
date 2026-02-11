const std = @import("std");
const table_builder = @import("table_builder.zig");

/// Table Decomposition for Lasso
///
/// Large lookup tables (e.g., 2^64 entries for 32-bit ADD) are infeasible to store.
/// We decompose them into smaller subtables that can be efficiently proved.
///
/// **Decomposition Strategies:**
/// - **Chunk16**: Break 32-bit values into two 16-bit chunks
/// - **Chunk8**: Break 32-bit values into four 8-bit chunks
/// - **Sparse**: Only store non-zero or interesting entries
/// - **Procedural**: Compute on-the-fly instead of storing
///
/// For example, 32-bit ADD(a, b) = c can be decomposed as:
///   a = a_lo || a_hi (16 bits each)
///   b = b_lo || b_hi
///   c = (a_lo + b_lo) + carry, (a_hi + b_hi + carry)
/// Now we have smaller 16-bit subtables and carry propagation logic.

pub const DecompositionStrategy = enum {
    Chunk16,
    Chunk8,
    Sparse,
    Procedural,
};

/// Decomposed value split into chunks
pub fn ChunkedValue(comptime num_chunks: usize) type {
    return struct {
        chunks: [num_chunks]u64,

        const Self = @This();

        /// Decompose a 32-bit value into 16-bit chunks
        pub fn fromU32_16bit(value: u32) Self {
            return Self{
                .chunks = [_]u64{
                    @as(u64, value & 0xFFFF), // Low 16 bits
                    @as(u64, (value >> 16) & 0xFFFF), // High 16 bits
                },
            };
        }

        /// Decompose a 32-bit value into 8-bit chunks
        pub fn fromU32_8bit(value: u32) Self {
            return Self{
                .chunks = [_]u64{
                    @as(u64, value & 0xFF),
                    @as(u64, (value >> 8) & 0xFF),
                    @as(u64, (value >> 16) & 0xFF),
                    @as(u64, (value >> 24) & 0xFF),
                },
            };
        }

        /// Recompose chunks back into 32-bit value (16-bit chunks)
        pub fn toU32_16bit(self: Self) u32 {
            return @as(u32, @intCast(self.chunks[0])) |
                (@as(u32, @intCast(self.chunks[1])) << 16);
        }

        /// Recompose chunks back into 32-bit value (8-bit chunks)
        pub fn toU32_8bit(self: Self) u32 {
            return @as(u32, @intCast(self.chunks[0])) |
                (@as(u32, @intCast(self.chunks[1])) << 8) |
                (@as(u32, @intCast(self.chunks[2])) << 16) |
                (@as(u32, @intCast(self.chunks[3])) << 24);
        }
    };
}

/// Subtable for decomposed operations
pub fn Subtable(comptime F: type) type {
    return struct {
        name: []const u8,
        chunk_bits: usize,
        entries: table_builder.DenseTable(F),

        const Self = @This();

        pub fn deinit(self: Self) void {
            self.entries.deinit();
        }

        /// Build subtable for 16-bit chunk addition with carry
        pub fn buildAdd16WithCarry(allocator: std.mem.Allocator) !Self {
            // Subtable: (a_chunk, b_chunk, carry_in) -> (sum_chunk, carry_out)
            // 3 inputs: two 16-bit chunks + 1-bit carry = 2^16 * 2^16 * 2 = 2^33 entries
            // This is still large but more manageable than 2^64

            const chunk_size: u64 = 1 << 16; // 65536 values per chunk
            const table_size = chunk_size * chunk_size * 2; // With carry_in = 0 or 1

            var entries = try table_builder.DenseTable(F).init(allocator, 3, 2, table_size);

            var idx: usize = 0;
            for (0..chunk_size) |a| {
                for (0..chunk_size) |b| {
                    for (0..2) |carry_in| {
                        const sum = a + b + carry_in;
                        const sum_chunk = sum & 0xFFFF;
                        const carry_out = (sum >> 16) & 1;

                        const inputs = try allocator.alloc(F, 3);
                        inputs[0] = F.init(@intCast(a));
                        inputs[1] = F.init(@intCast(b));
                        inputs[2] = F.init(@intCast(carry_in));

                        const outputs = try allocator.alloc(F, 2);
                        outputs[0] = F.init(@intCast(sum_chunk));
                        outputs[1] = F.init(@intCast(carry_out));

                        entries.entries[idx] = table_builder.TableEntry(F){
                            .inputs = inputs,
                            .outputs = outputs,
                        };
                        idx += 1;
                    }
                }
            }

            return Self{
                .name = "ADD16_CARRY",
                .chunk_bits = 16,
                .entries = entries,
            };
        }

        /// Build subtable for 8-bit chunk XOR (much smaller)
        pub fn buildXor8(allocator: std.mem.Allocator) !Self {
            // Subtable: (a_chunk, b_chunk) -> (result_chunk)
            // 2^8 * 2^8 = 2^16 = 65536 entries (very manageable!)

            const chunk_size: u64 = 1 << 8; // 256 values per chunk
            const table_size = chunk_size * chunk_size;

            var entries = try table_builder.DenseTable(F).init(allocator, 2, 1, table_size);

            var idx: usize = 0;
            for (0..chunk_size) |a| {
                for (0..chunk_size) |b| {
                    const result = a ^ b;

                    const inputs = try allocator.alloc(F, 2);
                    inputs[0] = F.init(@intCast(a));
                    inputs[1] = F.init(@intCast(b));

                    const outputs = try allocator.alloc(F, 1);
                    outputs[0] = F.init(@intCast(result));

                    entries.entries[idx] = table_builder.TableEntry(F){
                        .inputs = inputs,
                        .outputs = outputs,
                    };
                    idx += 1;
                }
            }

            return Self{
                .name = "XOR8",
                .chunk_bits = 8,
                .entries = entries,
            };
        }
    };
}

/// Decomposed table set for a full operation
pub fn DecomposedTable(comptime F: type) type {
    return struct {
        operation: []const u8,
        strategy: DecompositionStrategy,
        subtables: []Subtable(F),
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn deinit(self: Self) void {
            for (self.subtables) |subtable| {
                subtable.deinit();
            }
            self.allocator.free(self.subtables);
        }

        /// Create decomposed ADD table using Chunk16 strategy
        pub fn createAdd32Chunk16(allocator: std.mem.Allocator) !Self {
            // 32-bit ADD decomposed into:
            // 1. Low 16-bit addition with carry
            // 2. High 16-bit addition with carry from low

            var subtables = try allocator.alloc(Subtable(F), 1);
            subtables[0] = try Subtable(F).buildAdd16WithCarry(allocator);

            return Self{
                .operation = "ADD32",
                .strategy = .Chunk16,
                .subtables = subtables,
                .allocator = allocator,
            };
        }

        /// Create decomposed XOR table using Chunk8 strategy
        pub fn createXor32Chunk8(allocator: std.mem.Allocator) !Self {
            // 32-bit XOR decomposed into 4 independent 8-bit XOR operations

            var subtables = try allocator.alloc(Subtable(F), 1);
            subtables[0] = try Subtable(F).buildXor8(allocator);

            return Self{
                .operation = "XOR32",
                .strategy = .Chunk8,
                .subtables = subtables,
                .allocator = allocator,
            };
        }

        /// Compute memory usage of decomposed table
        pub fn memoryUsage(self: Self) usize {
            var total: usize = 0;
            for (self.subtables) |subtable| {
                const entry_size = subtable.entries.num_inputs + subtable.entries.num_outputs;
                total += subtable.entries.entries.len * entry_size * @sizeOf(F);
            }
            return total;
        }
    };
}

/// Decomposition metadata and cost analysis
pub const DecompositionAnalysis = struct {
    original_size: usize, // Size of full undecomposed table
    decomposed_size: usize, // Total size after decomposition
    num_subtables: usize,
    space_savings_factor: f64,

    pub fn analyze(original_bits: usize, strategy: DecompositionStrategy) DecompositionAnalysis {
        const original_size = (@as(usize, 1) << original_bits) * (@as(usize, 1) << original_bits);

        return switch (strategy) {
            .Chunk16 => {
                // 32-bit -> two 16-bit chunks
                // Subtable size: 2^16 * 2^16 * 2 (carry) = 2^33
                const subtable_size: usize = (@as(usize, 1) << 33);
                const num_subtables: usize = 1; // Just the add-with-carry subtable
                const decomposed_size = subtable_size * num_subtables;

                return DecompositionAnalysis{
                    .original_size = original_size,
                    .decomposed_size = decomposed_size,
                    .num_subtables = num_subtables,
                    .space_savings_factor = @as(f64, @floatFromInt(original_size)) /
                        @as(f64, @floatFromInt(decomposed_size)),
                };
            },
            .Chunk8 => {
                // 32-bit -> four 8-bit chunks
                // Subtable size: 2^8 * 2^8 = 2^16
                const subtable_size: usize = (@as(usize, 1) << 16);
                const num_subtables: usize = 1; // Shared 8-bit subtable
                const decomposed_size = subtable_size * num_subtables;

                return DecompositionAnalysis{
                    .original_size = original_size,
                    .decomposed_size = decomposed_size,
                    .num_subtables = num_subtables,
                    .space_savings_factor = @as(f64, @floatFromInt(original_size)) /
                        @as(f64, @floatFromInt(decomposed_size)),
                };
            },
            .Sparse => {
                // Sparse: only store non-trivial entries (assume 1% density)
                const sparse_size = original_size / 100;

                return DecompositionAnalysis{
                    .original_size = original_size,
                    .decomposed_size = sparse_size,
                    .num_subtables = 1,
                    .space_savings_factor = @as(f64, @floatFromInt(original_size)) /
                        @as(f64, @floatFromInt(sparse_size)),
                };
            },
            .Procedural => {
                // Procedural: no storage, compute on-the-fly
                return DecompositionAnalysis{
                    .original_size = original_size,
                    .decomposed_size = 0,
                    .num_subtables = 0,
                    .space_savings_factor = std.math.inf(f64),
                };
            },
        };
    }
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "decomposition: chunk 16-bit" {
    const ChunkedU32 = ChunkedValue(2);

    const value: u32 = 0x12345678;
    const chunked = ChunkedU32.fromU32_16bit(value);

    try testing.expectEqual(@as(u64, 0x5678), chunked.chunks[0]); // Low
    try testing.expectEqual(@as(u64, 0x1234), chunked.chunks[1]); // High

    const reconstructed = chunked.toU32_16bit();
    try testing.expectEqual(value, reconstructed);
}

test "decomposition: chunk 8-bit" {
    const ChunkedU32 = ChunkedValue(4);

    const value: u32 = 0x12345678;
    const chunked = ChunkedU32.fromU32_8bit(value);

    try testing.expectEqual(@as(u64, 0x78), chunked.chunks[0]);
    try testing.expectEqual(@as(u64, 0x56), chunked.chunks[1]);
    try testing.expectEqual(@as(u64, 0x34), chunked.chunks[2]);
    try testing.expectEqual(@as(u64, 0x12), chunked.chunks[3]);

    const reconstructed = chunked.toU32_8bit();
    try testing.expectEqual(value, reconstructed);
}

test "decomposition: xor8 subtable" {
    const F = field.Field(u64, 17);

    var subtable = try Subtable(F).buildXor8(testing.allocator);
    defer subtable.deinit();

    try testing.expectEqual(@as(usize, 8), subtable.chunk_bits);
    try testing.expectEqual(@as(usize, 65536), subtable.entries.entries.len);

    // Test: 0xAB XOR 0xCD = 0x66
    const inputs = [_]F{ F.init(0xAB), F.init(0xCD) };
    const result = subtable.entries.lookup(&inputs);
    try testing.expect(result != null);
    try testing.expect(result.?[0].eql(F.init(0x66)));
}

test "decomposition: decomposed xor32" {
    const F = field.Field(u64, 17);

    var decomposed = try DecomposedTable(F).createXor32Chunk8(testing.allocator);
    defer decomposed.deinit();

    try testing.expectEqual(@as(usize, 1), decomposed.subtables.len);

    // Memory usage should be reasonable
    const memory = decomposed.memoryUsage();
    try testing.expect(memory > 0);
}

test "decomposition: analysis chunk16" {
    const analysis = DecompositionAnalysis.analyze(32, .Chunk16);

    // Original: 2^64 entries
    // Decomposed: 2^33 entries
    // Savings: 2^31 = ~2 billion times smaller!
    try testing.expect(analysis.space_savings_factor > 1.0);
    try testing.expect(analysis.decomposed_size < analysis.original_size);
}

test "decomposition: analysis chunk8" {
    const analysis = DecompositionAnalysis.analyze(32, .Chunk8);

    // Chunk8 should give even better savings than Chunk16
    try testing.expect(analysis.space_savings_factor > 1.0);
    try testing.expect(analysis.decomposed_size < analysis.original_size);

    const chunk16_analysis = DecompositionAnalysis.analyze(32, .Chunk16);
    try testing.expect(analysis.space_savings_factor > chunk16_analysis.space_savings_factor);
}

test "decomposition: analysis sparse" {
    const analysis = DecompositionAnalysis.analyze(32, .Sparse);

    try testing.expect(analysis.space_savings_factor >= 100.0); // At least 100x savings
}

test "decomposition: analysis procedural" {
    const analysis = DecompositionAnalysis.analyze(32, .Procedural);

    try testing.expectEqual(@as(usize, 0), analysis.decomposed_size);
    try testing.expect(std.math.isInf(analysis.space_savings_factor));
}
