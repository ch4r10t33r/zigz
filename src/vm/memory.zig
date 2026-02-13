const std = @import("std");

/// Sparse Memory Model for RISC-V VM
///
/// Uses a HashMap to store only non-zero memory locations.
/// This is much more efficient than allocating 2^64 bytes!
///
/// Memory is byte-addressable, but we optimize by storing aligned words
/// when possible. Supports load/store of bytes, halfwords, words, and doublewords.

pub const Memory = struct {
    /// Sparse storage: only non-zero locations are stored
    /// Maps address → byte value
    data: std.AutoHashMap(u64, u8),

    /// Allocator for the hash map
    allocator: std.mem.Allocator,

    const Self = @This();

    /// Initialize empty memory
    pub fn init(allocator: std.mem.Allocator) Self {
        return Self{
            .data = std.AutoHashMap(u64, u8).init(allocator),
            .allocator = allocator,
        };
    }

    /// Clean up memory
    pub fn deinit(self: *Self) void {
        self.data.deinit();
    }

    /// Load a single byte from memory
    /// Returns 0 for uninitialized memory
    pub fn loadByte(self: Self, addr: u64) u8 {
        return self.data.get(addr) orelse 0;
    }

    /// Store a single byte to memory
    /// If value is 0, we can optionally remove it to keep storage sparse
    pub fn storeByte(self: *Self, addr: u64, value: u8) !void {
        if (value == 0) {
            _ = self.data.remove(addr); // Keep storage sparse
        } else {
            try self.data.put(addr, value);
        }
    }

    /// Load halfword (16 bits) - little endian
    pub fn loadHalfword(self: Self, addr: u64) u16 {
        const b0 = @as(u16, self.loadByte(addr));
        const b1 = @as(u16, self.loadByte(addr + 1));
        return b0 | (b1 << 8);
    }

    /// Store halfword (16 bits) - little endian
    pub fn storeHalfword(self: *Self, addr: u64, value: u16) !void {
        try self.storeByte(addr, @truncate(value));
        try self.storeByte(addr + 1, @truncate(value >> 8));
    }

    /// Load word (32 bits) - little endian
    pub fn loadWord(self: Self, addr: u64) u32 {
        const b0 = @as(u32, self.loadByte(addr));
        const b1 = @as(u32, self.loadByte(addr + 1));
        const b2 = @as(u32, self.loadByte(addr + 2));
        const b3 = @as(u32, self.loadByte(addr + 3));
        return b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
    }

    /// Store word (32 bits) - little endian
    pub fn storeWord(self: *Self, addr: u64, value: u32) !void {
        try self.storeByte(addr, @truncate(value));
        try self.storeByte(addr + 1, @truncate(value >> 8));
        try self.storeByte(addr + 2, @truncate(value >> 16));
        try self.storeByte(addr + 3, @truncate(value >> 24));
    }

    /// Load doubleword (64 bits) - little endian
    pub fn loadDoubleword(self: Self, addr: u64) u64 {
        const low = @as(u64, self.loadWord(addr));
        const high = @as(u64, self.loadWord(addr + 4));
        return low | (high << 32);
    }

    /// Store doubleword (64 bits) - little endian
    pub fn storeDoubleword(self: *Self, addr: u64, value: u64) !void {
        try self.storeWord(addr, @truncate(value));
        try self.storeWord(addr + 4, @truncate(value >> 32));
    }

    /// Load with sign extension (for LB, LH, LW)
    pub fn loadSignExtended(self: Self, addr: u64, size: LoadSize) i64 {
        return switch (size) {
            .Byte => blk: {
                const val = self.loadByte(addr);
                break :blk @as(i64, @as(i8, @bitCast(val)));
            },
            .Halfword => blk: {
                const val = self.loadHalfword(addr);
                break :blk @as(i64, @as(i16, @bitCast(val)));
            },
            .Word => blk: {
                const val = self.loadWord(addr);
                break :blk @as(i64, @as(i32, @bitCast(val)));
            },
            .Doubleword => blk: {
                const val = self.loadDoubleword(addr);
                break :blk @as(i64, @bitCast(val));
            },
        };
    }

    /// Load with zero extension (for LBU, LHU, LWU)
    pub fn loadZeroExtended(self: Self, addr: u64, size: LoadSize) u64 {
        return switch (size) {
            .Byte => @as(u64, self.loadByte(addr)),
            .Halfword => @as(u64, self.loadHalfword(addr)),
            .Word => @as(u64, self.loadWord(addr)),
            .Doubleword => self.loadDoubleword(addr),
        };
    }

    /// Store data of various sizes
    pub fn store(self: *Self, addr: u64, value: u64, size: LoadSize) !void {
        switch (size) {
            .Byte => try self.storeByte(addr, @truncate(value)),
            .Halfword => try self.storeHalfword(addr, @truncate(value)),
            .Word => try self.storeWord(addr, @truncate(value)),
            .Doubleword => try self.storeDoubleword(addr, value),
        }
    }

    /// Load program into memory at given address
    pub fn loadProgram(self: *Self, start_addr: u64, program: []const u8) !void {
        for (program, 0..) |byte, i| {
            try self.storeByte(start_addr + i, byte);
        }
    }

    /// Get memory usage statistics
    pub fn stats(self: Self) MemoryStats {
        return MemoryStats{
            .allocated_bytes = self.data.count(),
            .hash_map_capacity = self.data.capacity(),
        };
    }

    /// Create a snapshot of memory state (for execution trace)
    /// Only copies non-zero locations
    pub fn snapshot(self: Self) !Self {
        var copy = Self.init(self.allocator);

        var iter = self.data.iterator();
        while (iter.next()) |entry| {
            try copy.data.put(entry.key_ptr.*, entry.value_ptr.*);
        }

        return copy;
    }
};

/// Load/Store sizes
pub const LoadSize = enum {
    Byte,      // 8 bits
    Halfword,  // 16 bits
    Word,      // 32 bits
    Doubleword, // 64 bits (RV64I)
};

/// Memory statistics
pub const MemoryStats = struct {
    allocated_bytes: usize,
    hash_map_capacity: usize,
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "memory: load uninitialized returns zero" {
    const mem = Memory.init(testing.allocator);
    defer {
        var m = mem;
        m.deinit();
    }

    // Uninitialized memory should return 0
    try testing.expectEqual(@as(u8, 0), mem.loadByte(0x1000));
    try testing.expectEqual(@as(u32, 0), mem.loadWord(0x2000));
    try testing.expectEqual(@as(u64, 0), mem.loadDoubleword(0x3000));
}

test "memory: byte load/store" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    try mem.storeByte(0x1000, 0x42);
    try testing.expectEqual(@as(u8, 0x42), mem.loadByte(0x1000));
}

test "memory: word load/store (32-bit)" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    try mem.storeWord(0x1000, 0xDEADBEEF);
    try testing.expectEqual(@as(u32, 0xDEADBEEF), mem.loadWord(0x1000));

    // Check little-endian byte order
    try testing.expectEqual(@as(u8, 0xEF), mem.loadByte(0x1000));
    try testing.expectEqual(@as(u8, 0xBE), mem.loadByte(0x1001));
    try testing.expectEqual(@as(u8, 0xAD), mem.loadByte(0x1002));
    try testing.expectEqual(@as(u8, 0xDE), mem.loadByte(0x1003));
}

test "memory: doubleword load/store (64-bit)" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    try mem.storeDoubleword(0x1000, 0x0123456789ABCDEF);
    try testing.expectEqual(@as(u64, 0x0123456789ABCDEF), mem.loadDoubleword(0x1000));
}

test "memory: sign extension" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    // Store -1 as a byte (0xFF)
    try mem.storeByte(0x1000, 0xFF);

    // Load with sign extension should give -1
    const signed_val = mem.loadSignExtended(0x1000, .Byte);
    try testing.expectEqual(@as(i64, -1), signed_val);

    // Load with zero extension should give 255
    const unsigned_val = mem.loadZeroExtended(0x1000, .Byte);
    try testing.expectEqual(@as(u64, 255), unsigned_val);
}

test "memory: sparse storage efficiency" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    // Store data at sparse addresses
    try mem.storeByte(0x1000, 0x42);
    try mem.storeByte(0x100000, 0x43);
    try mem.storeByte(0x10000000, 0x44);

    const mem_stats = mem.stats();

    // Should only have 3 bytes allocated, not the full address range
    try testing.expectEqual(@as(usize, 3), mem_stats.allocated_bytes);
}

test "memory: store zero removes entry" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    // Store non-zero value
    try mem.storeByte(0x1000, 0x42);
    try testing.expectEqual(@as(usize, 1), mem.stats().allocated_bytes);

    // Overwrite with zero should remove the entry
    try mem.storeByte(0x1000, 0x00);
    try testing.expectEqual(@as(usize, 0), mem.stats().allocated_bytes);
}

test "memory: load program" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    const program = [_]u8{ 0x13, 0x05, 0x00, 0x00 }; // ADDI x10, x0, 0

    try mem.loadProgram(0x1000, &program);

    // Check program loaded correctly
    for (program, 0..) |byte, i| {
        try testing.expectEqual(byte, mem.loadByte(0x1000 + i));
    }
}

test "memory: snapshot creates independent copy" {
    var mem = Memory.init(testing.allocator);
    defer mem.deinit();

    try mem.storeByte(0x1000, 0x42);

    var snapshot = try mem.snapshot();
    defer snapshot.deinit();

    // Modify original
    try mem.storeByte(0x1000, 0x99);

    // Snapshot should have old value
    try testing.expectEqual(@as(u8, 0x42), snapshot.loadByte(0x1000));

    // Original should have new value
    try testing.expectEqual(@as(u8, 0x99), mem.loadByte(0x1000));
}
