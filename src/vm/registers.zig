const std = @import("std");

/// RISC-V RV64I Register File
///
/// Implements the 32 general-purpose integer registers (x0-x31).
/// - x0 is hardwired to zero (reads always return 0, writes are ignored)
/// - x1-x31 are general-purpose 64-bit registers
///
/// Special register conventions (ABI):
/// - x0 (zero): Hard-wired zero
/// - x1 (ra): Return address
/// - x2 (sp): Stack pointer
/// - x3 (gp): Global pointer
/// - x4 (tp): Thread pointer
/// - x5-x7 (t0-t2): Temporaries
/// - x8 (s0/fp): Saved register / Frame pointer
/// - x9 (s1): Saved register
/// - x10-x11 (a0-a1): Function arguments / Return values
/// - x12-x17 (a2-a7): Function arguments
/// - x18-x27 (s2-s11): Saved registers
/// - x28-x31 (t3-t6): Temporaries

pub const RegisterFile = struct {
    /// 32 general-purpose registers (x0-x31)
    /// x0 is handled specially and always reads as 0
    regs: [32]u64,

    const Self = @This();

    /// Initialize register file with all zeros
    pub fn init() Self {
        return Self{
            .regs = [_]u64{0} ** 32,
        };
    }

    /// Read a register value
    /// x0 always returns 0, regardless of what's stored
    pub fn read(self: Self, reg: u5) u64 {
        if (reg == 0) return 0;
        return self.regs[reg];
    }

    /// Write a register value
    /// Writes to x0 are silently ignored (as per RISC-V spec)
    pub fn write(self: *Self, reg: u5, value: u64) void {
        if (reg == 0) return; // x0 is hardwired to zero
        self.regs[reg] = value;
    }

    /// Get register name for debugging
    pub fn name(reg: u5) []const u8 {
        return switch (reg) {
            0 => "zero",
            1 => "ra",
            2 => "sp",
            3 => "gp",
            4 => "tp",
            5 => "t0",
            6 => "t1",
            7 => "t2",
            8 => "s0/fp",
            9 => "s1",
            10 => "a0",
            11 => "a1",
            12 => "a2",
            13 => "a3",
            14 => "a4",
            15 => "a5",
            16 => "a6",
            17 => "a7",
            18 => "s2",
            19 => "s3",
            20 => "s4",
            21 => "s5",
            22 => "s6",
            23 => "s7",
            24 => "s8",
            25 => "s9",
            26 => "s10",
            27 => "s11",
            28 => "t3",
            29 => "t4",
            30 => "t5",
            31 => "t6",
        };
    }

    /// Copy register state (for snapshots in execution trace)
    pub fn snapshot(self: Self) Self {
        return Self{
            .regs = self.regs,
        };
    }

    /// Format register file for debugging
    pub fn format(
        self: Self,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;

        try writer.writeAll("Registers:\n");
        var i: u5 = 0;
        while (i < 32) : (i += 1) {
            const val = self.read(i);
            if (val != 0 or i == 0) { // Only show non-zero registers
                try writer.print("  x{d:2} ({s:6}): 0x{x:016}\n", .{ i, name(i), val });
            }
        }
    }
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "registers: x0 always reads as zero" {
    var regs = RegisterFile.init();

    // Try to write to x0
    regs.write(0, 0xDEADBEEF);

    // x0 should still be zero
    try testing.expectEqual(@as(u64, 0), regs.read(0));
}

test "registers: read/write general purpose registers" {
    var regs = RegisterFile.init();

    // Write and read x1
    regs.write(1, 0x1234567890ABCDEF);
    try testing.expectEqual(@as(u64, 0x1234567890ABCDEF), regs.read(1));

    // Write and read x31
    regs.write(31, 0xFEDCBA0987654321);
    try testing.expectEqual(@as(u64, 0xFEDCBA0987654321), regs.read(31));
}

test "registers: initialization to zero" {
    const regs = RegisterFile.init();

    // All registers should be zero initially
    for (0..32) |i| {
        try testing.expectEqual(@as(u64, 0), regs.read(@intCast(i)));
    }
}

test "registers: snapshot preserves state" {
    var regs = RegisterFile.init();

    regs.write(10, 100);
    regs.write(11, 200);

    const snapshot = regs.snapshot();

    // Modify original
    regs.write(10, 999);

    // Snapshot should have old values
    try testing.expectEqual(@as(u64, 100), snapshot.read(10));
    try testing.expectEqual(@as(u64, 200), snapshot.read(11));

    // Original should have new values
    try testing.expectEqual(@as(u64, 999), regs.read(10));
}

test "registers: all register names defined" {
    for (0..32) |i| {
        const reg_name = RegisterFile.name(@intCast(i));
        try testing.expect(reg_name.len > 0);
    }
}
