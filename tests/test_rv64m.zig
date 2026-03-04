const std = @import("std");
const testing = std.testing;
const zigz = @import("zigz");

/// RV64M extension tests
///
/// Tests the multiply/divide operations added by RV64M:
/// - MUL, MULH, MULHSU, MULHU (multiply)
/// - DIV, DIVU, REM, REMU (divide/remainder)
/// - MULW, DIVW, DIVUW, REMW, REMUW (word variants)

test "rv64m: MUL (multiply lower 64 bits)" {
    // Test basic multiplication
    //
    // LI x10, 6
    // LI x11, 7
    // MUL x12, x10, x11     # x12 = 6 * 7 = 42

    const program = [_]u8{
        // ADDI x10, x0, 6
        0x13, 0x05, 0x60, 0x00,
        // ADDI x11, x0, 7
        0x93, 0x05, 0x70, 0x00,
        // MUL x12, x10, x11 (OP opcode, funct3=0b000, funct7=0b0000001)
        0x33, 0x06, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 42), vm.regs.read(12));
}

test "rv64m: MULH (signed × signed, upper 64 bits)" {
    // Test signed high multiply
    //
    // LI x10, -1 (0xFFFFFFFFFFFFFFFF)
    // LI x11, -1
    // MULH x12, x10, x11     # High 64 bits of (-1) * (-1)

    const program = [_]u8{
        // ADDI x10, x0, -1
        0x13, 0x05, 0xF0, 0xFF,
        // ADDI x11, x0, -1
        0x93, 0x05, 0xF0, 0xFF,
        // MULH x12, x10, x11 (funct3=0b001, funct7=0b0000001)
        0x33, 0x16, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    // (-1) * (-1) = 1, high 64 bits = 0
    try testing.expectEqual(@as(u64, 0), vm.regs.read(12));
}

test "rv64m: MULHU (unsigned × unsigned, upper 64 bits)" {
    // Test unsigned high multiply
    //
    // LI x10, 0xFFFFFFFFFFFFFFFF
    // LI x11, 2
    // MULHU x12, x10, x11    # High 64 bits of (2^64-1) * 2

    const program = [_]u8{
        // ADDI x10, x0, -1 (0xFFFFFFFFFFFFFFFF)
        0x13, 0x05, 0xF0, 0xFF,
        // ADDI x11, x0, 2
        0x93, 0x05, 0x20, 0x00,
        // MULHU x12, x10, x11 (funct3=0b011, funct7=0b0000001)
        0x33, 0x36, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    // 0xFFFFFFFFFFFFFFFF * 2 = 0x1FFFFFFFFFFFFFFFE
    // High 64 bits = 1
    try testing.expectEqual(@as(u64, 1), vm.regs.read(12));
}

test "rv64m: DIV (signed division)" {
    // Test signed division
    //
    // LI x10, 20
    // LI x11, 3
    // DIV x12, x10, x11      # x12 = 20 / 3 = 6

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // DIV x12, x10, x11 (funct3=0b100, funct7=0b0000001)
        0x33, 0x46, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 6), vm.regs.read(12));
}

test "rv64m: DIV by zero" {
    // Test division by zero behavior (should return -1)
    //
    // LI x10, 20
    // LI x11, 0
    // DIV x12, x10, x11      # x12 = -1 (division by zero)

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 0
        0x93, 0x05, 0x00, 0x00,
        // DIV x12, x10, x11
        0x33, 0x46, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    // Division by zero returns -1
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFF), vm.regs.read(12));
}

test "rv64m: DIVU (unsigned division)" {
    // Test unsigned division
    //
    // LI x10, 20
    // LI x11, 3
    // DIVU x12, x10, x11     # x12 = 20 / 3 = 6

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // DIVU x12, x10, x11 (funct3=0b101, funct7=0b0000001)
        0x33, 0x56, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 6), vm.regs.read(12));
}

test "rv64m: REM (signed remainder)" {
    // Test signed remainder
    //
    // LI x10, 20
    // LI x11, 3
    // REM x12, x10, x11      # x12 = 20 % 3 = 2

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // REM x12, x10, x11 (funct3=0b110, funct7=0b0000001)
        0x33, 0x66, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 2), vm.regs.read(12));
}

test "rv64m: REMU (unsigned remainder)" {
    // Test unsigned remainder
    //
    // LI x10, 20
    // LI x11, 3
    // REMU x12, x10, x11     # x12 = 20 % 3 = 2

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // REMU x12, x10, x11 (funct3=0b111, funct7=0b0000001)
        0x33, 0x76, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 2), vm.regs.read(12));
}

test "rv64m: MULW (multiply word)" {
    // Test 32-bit multiply with sign extension
    //
    // LI x10, 6
    // LI x11, 7
    // MULW x12, x10, x11     # x12 = 6 * 7 = 42 (sign-extended)

    const program = [_]u8{
        // ADDI x10, x0, 6
        0x13, 0x05, 0x60, 0x00,
        // ADDI x11, x0, 7
        0x93, 0x05, 0x70, 0x00,
        // MULW x12, x10, x11 (OP_32 opcode, funct3=0b000, funct7=0b0000001)
        0x3B, 0x06, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 42), vm.regs.read(12));
}

test "rv64m: MULW overflow" {
    // Test that MULW sign-extends negative results
    //
    // LI x10, 0x7FFFFFFF (max positive 32-bit)
    // LI x11, 2
    // MULW x12, x10, x11     # Overflows to negative

    const program = [_]u8{
        // LUI x10, 0x80000
        0x37, 0x05, 0x00, 0x80,
        // ADDI x10, x10, -1 (0x7FFFFFFF)
        0x13, 0x05, 0xF5, 0xFF,
        // ADDI x11, x0, 2
        0x93, 0x05, 0x20, 0x00,
        // MULW x12, x10, x11
        0x3B, 0x06, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(4);

    // 0x7FFFFFFF * 2 = 0xFFFFFFFE (negative when viewed as i32, sign-extended)
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFE), vm.regs.read(12));
}

test "rv64m: DIVW (signed word division)" {
    // Test 32-bit signed division
    //
    // LI x10, 20
    // LI x11, 3
    // DIVW x12, x10, x11     # x12 = 20 / 3 = 6

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // DIVW x12, x10, x11 (funct3=0b100, funct7=0b0000001)
        0x3B, 0x46, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 6), vm.regs.read(12));
}

test "rv64m: DIVUW (unsigned word division)" {
    // Test 32-bit unsigned division
    //
    // LI x10, 20
    // LI x11, 3
    // DIVUW x12, x10, x11    # x12 = 20 / 3 = 6

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // DIVUW x12, x10, x11 (funct3=0b101, funct7=0b0000001)
        0x3B, 0x56, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 6), vm.regs.read(12));
}

test "rv64m: REMW (signed word remainder)" {
    // Test 32-bit signed remainder
    //
    // LI x10, 20
    // LI x11, 3
    // REMW x12, x10, x11     # x12 = 20 % 3 = 2

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // REMW x12, x10, x11 (funct3=0b110, funct7=0b0000001)
        0x3B, 0x66, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 2), vm.regs.read(12));
}

test "rv64m: REMUW (unsigned word remainder)" {
    // Test 32-bit unsigned remainder
    //
    // LI x10, 20
    // LI x11, 3
    // REMUW x12, x10, x11    # x12 = 20 % 3 = 2

    const program = [_]u8{
        // ADDI x10, x0, 20
        0x13, 0x05, 0x40, 0x01,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // REMUW x12, x10, x11 (funct3=0b111, funct7=0b0000001)
        0x3B, 0x76, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 2), vm.regs.read(12));
}

test "rv64m: Negative number multiplication" {
    // Test multiplication with negative numbers
    //
    // LI x10, -5
    // LI x11, 3
    // MUL x12, x10, x11      # x12 = -5 * 3 = -15

    const program = [_]u8{
        // ADDI x10, x0, -5
        0x13, 0x05, 0xB0, 0xFF,
        // ADDI x11, x0, 3
        0x93, 0x05, 0x30, 0x00,
        // MUL x12, x10, x11
        0x33, 0x06, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    // -15 in 64-bit two's complement
    const expected: u64 = @bitCast(@as(i64, -15));
    try testing.expectEqual(expected, vm.regs.read(12));
}

test "rv64m: Large number multiplication" {
    // Test multiplication with large numbers requiring high bits
    //
    // LI x10, 0x100000000 (2^32)
    // LI x11, 0x100000000 (2^32)
    // MUL x12, x10, x11      # Low 64 bits = 0
    // MULHU x13, x10, x11    # High 64 bits = 1

    const program = [_]u8{
        // LUI x10, 0x00010
        0x37, 0x05, 0x01, 0x00,
        // SLLI x10, x10, 20 (shift to get 2^32)
        0x13, 0x15, 0x45, 0x01,
        // LUI x11, 0x00010
        0xB7, 0x05, 0x01, 0x00,
        // SLLI x11, x11, 20
        0x93, 0x15, 0x45, 0x01,
        // MUL x12, x10, x11
        0x33, 0x06, 0xB5, 0x02,
        // MULHU x13, x10, x11
        0xB3, 0x36, 0xB5, 0x02,
    };

    var vm = try zigz.VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(6);

    // 2^32 * 2^32 = 2^64 = 0x10000000000000000
    // Low 64 bits = 0
    try testing.expectEqual(@as(u64, 0), vm.regs.read(12));
    // High 64 bits = 1
    try testing.expectEqual(@as(u64, 1), vm.regs.read(13));
}
