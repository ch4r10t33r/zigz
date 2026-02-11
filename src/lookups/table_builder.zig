const std = @import("std");
const rv32i = @import("../isa/rv32i.zig");
const instruction_table = @import("../isa/instruction_table.zig");

/// Lookup Table Builder
///
/// Constructs lookup tables for RISC-V instructions. Each table maps
/// (input values) -> (output values) for a specific operation.
///
/// For example, an ADD table would map (a, b) -> a + b for all valid inputs.
/// Since full tables can be massive (2^64 entries for 32-bit ADD), we use
/// decomposition strategies to make them tractable.

/// Table entry representing a single (input, output) pair
pub fn TableEntry(comptime F: type) type {
    return struct {
        inputs: []F,
        outputs: []F,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator, input_values: []const F, output_values: []const F) !Self {
            const inputs = try allocator.dupe(F, input_values);
            const outputs = try allocator.dupe(F, output_values);
            return Self{
                .inputs = inputs,
                .outputs = outputs,
            };
        }

        pub fn deinit(self: Self, allocator: std.mem.Allocator) void {
            allocator.free(self.inputs);
            allocator.free(self.outputs);
        }
    };
}

/// Dense lookup table stored as array of entries
pub fn DenseTable(comptime F: type) type {
    return struct {
        entries: []TableEntry(F),
        num_inputs: usize,
        num_outputs: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator, num_inputs: usize, num_outputs: usize, size: usize) !Self {
            const entries = try allocator.alloc(TableEntry(F), size);
            return Self{
                .entries = entries,
                .num_inputs = num_inputs,
                .num_outputs = num_outputs,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: Self) void {
            for (self.entries) |entry| {
                entry.deinit(self.allocator);
            }
            self.allocator.free(self.entries);
        }

        /// Lookup output for given input
        pub fn lookup(self: Self, inputs: []const F) ?[]const F {
            for (self.entries) |entry| {
                if (entry.inputs.len != inputs.len) continue;

                var matches = true;
                for (entry.inputs, inputs) |a, b| {
                    if (!a.eql(b)) {
                        matches = false;
                        break;
                    }
                }

                if (matches) {
                    return entry.outputs;
                }
            }
            return null;
        }
    };
}

/// Sparse lookup table using hash map
pub fn SparseTable(comptime F: type) type {
    return struct {
        map: std.AutoHashMap(u64, TableEntry(F)),
        num_inputs: usize,
        num_outputs: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator, num_inputs: usize, num_outputs: usize) !Self {
            return Self{
                .map = std.AutoHashMap(u64, TableEntry(F)).init(allocator),
                .num_inputs = num_inputs,
                .num_outputs = num_outputs,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            var iter = self.map.valueIterator();
            while (iter.next()) |entry| {
                entry.deinit(self.allocator);
            }
            self.map.deinit();
        }

        /// Insert entry into table
        pub fn insert(self: *Self, key: u64, entry: TableEntry(F)) !void {
            try self.map.put(key, entry);
        }

        /// Lookup output for given input key
        pub fn lookup(self: Self, key: u64) ?TableEntry(F) {
            return self.map.get(key);
        }
    };
}

/// Build ADD lookup table (small example for testing)
pub fn buildAddTable(comptime F: type, allocator: std.mem.Allocator, bits: usize) !DenseTable(F) {
    const size = @as(usize, 1) << (bits * 2); // 2^(2*bits) entries for (a, b)
    var table = try DenseTable(F).init(allocator, 2, 1, size);

    const max_val = @as(u64, 1) << @intCast(bits);
    var idx: usize = 0;

    for (0..max_val) |a| {
        for (0..max_val) |b| {
            const sum = (a + b) % max_val; // Wrap around at 2^bits

            const inputs = try allocator.alloc(F, 2);
            inputs[0] = F.init(@intCast(a));
            inputs[1] = F.init(@intCast(b));

            const outputs = try allocator.alloc(F, 1);
            outputs[0] = F.init(@intCast(sum));

            table.entries[idx] = TableEntry(F){
                .inputs = inputs,
                .outputs = outputs,
            };
            idx += 1;
        }
    }

    return table;
}

/// Build XOR lookup table (small example for testing)
pub fn buildXorTable(comptime F: type, allocator: std.mem.Allocator, bits: usize) !DenseTable(F) {
    const size = @as(usize, 1) << (bits * 2);
    var table = try DenseTable(F).init(allocator, 2, 1, size);

    const max_val = @as(u64, 1) << @intCast(bits);
    var idx: usize = 0;

    for (0..max_val) |a| {
        for (0..max_val) |b| {
            const result = a ^ b;

            const inputs = try allocator.alloc(F, 2);
            inputs[0] = F.init(@intCast(a));
            inputs[1] = F.init(@intCast(b));

            const outputs = try allocator.alloc(F, 1);
            outputs[0] = F.init(@intCast(result));

            table.entries[idx] = TableEntry(F){
                .inputs = inputs,
                .outputs = outputs,
            };
            idx += 1;
        }
    }

    return table;
}

/// Build AND lookup table (small example for testing)
pub fn buildAndTable(comptime F: type, allocator: std.mem.Allocator, bits: usize) !DenseTable(F) {
    const size = @as(usize, 1) << (bits * 2);
    var table = try DenseTable(F).init(allocator, 2, 1, size);

    const max_val = @as(u64, 1) << @intCast(bits);
    var idx: usize = 0;

    for (0..max_val) |a| {
        for (0..max_val) |b| {
            const result = a & b;

            const inputs = try allocator.alloc(F, 2);
            inputs[0] = F.init(@intCast(a));
            inputs[1] = F.init(@intCast(b));

            const outputs = try allocator.alloc(F, 1);
            outputs[0] = F.init(@intCast(result));

            table.entries[idx] = TableEntry(F){
                .inputs = inputs,
                .outputs = outputs,
            };
            idx += 1;
        }
    }

    return table;
}

/// Build sparse table for conditional operations (e.g., BEQ when taken)
pub fn buildSparseConditionalTable(comptime F: type, allocator: std.mem.Allocator) !SparseTable(F) {
    var table = try SparseTable(F).init(allocator, 2, 1);

    // Only store entries where condition is true (a == b)
    for (0..256) |a| {
        const key = (a << 8) | a; // Hash of (a, a)

        const inputs = try allocator.alloc(F, 2);
        inputs[0] = F.init(@intCast(a));
        inputs[1] = F.init(@intCast(a));

        const outputs = try allocator.alloc(F, 1);
        outputs[0] = F.init(1); // Branch taken

        const entry = TableEntry(F){
            .inputs = inputs,
            .outputs = outputs,
        };

        try table.insert(key, entry);
    }

    return table;
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const field = @import("../core/field.zig");

test "table_builder: dense table creation" {
    const F = field.Field(u64, 17);

    var table = try DenseTable(F).init(testing.allocator, 2, 1, 4);
    defer table.deinit();

    try testing.expectEqual(@as(usize, 4), table.entries.len);
    try testing.expectEqual(@as(usize, 2), table.num_inputs);
    try testing.expectEqual(@as(usize, 1), table.num_outputs);
}

test "table_builder: add table 2-bit" {
    const F = field.Field(u64, 17);

    var table = try buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    // Table should have 2^4 = 16 entries (4 values × 4 values)
    try testing.expectEqual(@as(usize, 16), table.entries.len);

    // Test: 2 + 3 = 5 mod 4 = 1
    const inputs = [_]F{ F.init(2), F.init(3) };
    const result = table.lookup(&inputs);
    try testing.expect(result != null);
    try testing.expect(result.?[0].eql(F.init(1)));
}

test "table_builder: xor table 3-bit" {
    const F = field.Field(u64, 17);

    var table = try buildXorTable(F, testing.allocator, 3);
    defer table.deinit();

    // Table should have 2^6 = 64 entries (8 values × 8 values)
    try testing.expectEqual(@as(usize, 64), table.entries.len);

    // Test: 5 XOR 3 = 6
    const inputs = [_]F{ F.init(5), F.init(3) };
    const result = table.lookup(&inputs);
    try testing.expect(result != null);
    try testing.expect(result.?[0].eql(F.init(6)));
}

test "table_builder: and table 2-bit" {
    const F = field.Field(u64, 17);

    var table = try buildAndTable(F, testing.allocator, 2);
    defer table.deinit();

    // Test: 3 AND 2 = 2
    const inputs = [_]F{ F.init(3), F.init(2) };
    const result = table.lookup(&inputs);
    try testing.expect(result != null);
    try testing.expect(result.?[0].eql(F.init(2)));
}

test "table_builder: sparse table" {
    const F = field.Field(u64, 17);

    var table = try buildSparseConditionalTable(F, testing.allocator);
    defer table.deinit();

    // Lookup existing entry (5, 5)
    const key1: u64 = (5 << 8) | 5;
    const result1 = table.lookup(key1);
    try testing.expect(result1 != null);
    try testing.expect(result1.?.outputs[0].eql(F.init(1)));

    // Lookup non-existing entry (5, 6)
    const key2: u64 = (5 << 8) | 6;
    const result2 = table.lookup(key2);
    try testing.expect(result2 == null);
}

test "table_builder: lookup miss" {
    const F = field.Field(u64, 17);

    var table = try buildAddTable(F, testing.allocator, 2);
    defer table.deinit();

    // Lookup with out-of-range input (should not find)
    const inputs = [_]F{ F.init(10), F.init(11) };
    const result = table.lookup(&inputs);
    try testing.expect(result == null);
}

test "table_builder: table entry lifecycle" {
    const F = field.Field(u64, 17);

    const inputs = try testing.allocator.alloc(F, 2);
    inputs[0] = F.init(1);
    inputs[1] = F.init(2);

    const outputs = try testing.allocator.alloc(F, 1);
    outputs[0] = F.init(3);

    const entry = TableEntry(F){
        .inputs = inputs,
        .outputs = outputs,
    };

    try testing.expectEqual(@as(usize, 2), entry.inputs.len);
    try testing.expectEqual(@as(usize, 1), entry.outputs.len);
    try testing.expect(entry.outputs[0].eql(F.init(3)));

    entry.deinit(testing.allocator);
}
