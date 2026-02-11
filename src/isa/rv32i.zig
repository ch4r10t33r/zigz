const std = @import("std");

/// RISC-V RV32I Base Integer Instruction Set
///
/// This module implements the RV32I base instruction set - the foundational
/// 32-bit RISC-V instructions. RV32I is minimal yet complete, providing:
/// - Integer computation
/// - Load/store operations
/// - Control flow (branches and jumps)
/// - System instructions
///
/// Reference: RISC-V Instruction Set Manual, Volume I: User-Level ISA
/// https://riscv.org/technical/specifications/

/// RISC-V instruction formats
///
/// RV32I uses 6 instruction formats, each encoding different fields:
/// - R-type: Register-register operations (add, sub, etc.)
/// - I-type: Immediate operations (addi, load, etc.)
/// - S-type: Store operations
/// - B-type: Branch operations
/// - U-type: Upper immediate (lui, auipc)
/// - J-type: Jump (jal)
pub const InstructionFormat = enum {
    R, // Register-register
    I, // Immediate
    S, // Store
    B, // Branch
    U, // Upper immediate
    J, // Jump
};

/// RV32I Opcodes (bits [6:0])
pub const Opcode = enum(u7) {
    LOAD = 0b0000011,
    LOAD_FP = 0b0000111,
    MISC_MEM = 0b0001111,
    OP_IMM = 0b0010011,
    AUIPC = 0b0010111,
    OP_IMM_32 = 0b0011011,
    STORE = 0b0100011,
    STORE_FP = 0b0100111,
    AMO = 0b0101111,
    OP = 0b0110011,
    LUI = 0b0110111,
    OP_32 = 0b0111011,
    MADD = 0b1000011,
    MSUB = 0b1000111,
    NMSUB = 0b1001011,
    NMADD = 0b1001111,
    OP_FP = 0b1010011,
    BRANCH = 0b1100011,
    JALR = 0b1100111,
    JAL = 0b1101111,
    SYSTEM = 0b1110011,

    /// Get the instruction format for this opcode
    pub fn format(self: Opcode) InstructionFormat {
        return switch (self) {
            .OP, .OP_32 => .R,
            .OP_IMM, .OP_IMM_32, .JALR, .LOAD, .MISC_MEM, .SYSTEM => .I,
            .STORE, .STORE_FP => .S,
            .BRANCH => .B,
            .LUI, .AUIPC => .U,
            .JAL => .J,
            else => .R, // Default
        };
    }
};

/// Function codes for R-type and I-type instructions
pub const Funct3 = enum(u3) {
    // ALU operations
    ADD_SUB = 0b000,
    SLL = 0b001,
    SLT = 0b010,
    SLTU = 0b011,
    XOR = 0b100,
    SRL_SRA = 0b101,
    OR = 0b110,
    AND = 0b111,

    // Load/Store widths
    BYTE = 0b000, // LB/SB
    HALF = 0b001, // LH/SH
    WORD = 0b010, // LW/SW
    BYTE_U = 0b100, // LBU
    HALF_U = 0b101, // LHU

    // Branch conditions
    BEQ = 0b000,
    BNE = 0b001,
    BLT = 0b100,
    BGE = 0b101,
    BLTU = 0b110,
    BGEU = 0b111,

    // MISC_MEM
    FENCE = 0b000,

    // SYSTEM
    PRIV = 0b000,
};

/// Function codes for R-type instructions (funct7)
pub const Funct7 = enum(u7) {
    NORM = 0b0000000, // Normal operations (add, sll, etc.)
    ALT = 0b0100000, // Alternative (sub, sra)
    MULDIV = 0b0000001, // Multiply/divide extension
};

/// Decoded RISC-V instruction
///
/// Contains all fields extracted from a 32-bit instruction word
pub const Instruction = struct {
    /// Raw 32-bit instruction word
    raw: u32,

    /// Instruction format
    format: InstructionFormat,

    /// Opcode (bits [6:0])
    opcode: Opcode,

    /// Destination register (bits [11:7])
    rd: u5,

    /// Function code 3 (bits [14:12])
    funct3: u3,

    /// Source register 1 (bits [19:15])
    rs1: u5,

    /// Source register 2 (bits [24:20])
    rs2: u5,

    /// Function code 7 (bits [31:25])
    funct7: u7,

    /// Immediate value (decoded based on format)
    imm: i32,

    /// Decode a 32-bit instruction word
    pub fn decode(word: u32) !Instruction {
        // Extract opcode (bits [6:0])
        const opcode_val = @as(u7, @truncate(word & 0x7F));
        const opcode = std.meta.intToEnum(Opcode, opcode_val) catch {
            return error.InvalidOpcode;
        };

        const format = opcode.format();

        // Extract common fields
        const rd = @as(u5, @truncate((word >> 7) & 0x1F));
        const funct3 = @as(u3, @truncate((word >> 12) & 0x07));
        const rs1 = @as(u5, @truncate((word >> 15) & 0x1F));
        const rs2 = @as(u5, @truncate((word >> 20) & 0x1F));
        const funct7 = @as(u7, @truncate((word >> 25) & 0x7F));

        // Decode immediate based on format
        const imm = decodeImmediate(word, format);

        return Instruction{
            .raw = word,
            .format = format,
            .opcode = opcode,
            .rd = rd,
            .funct3 = funct3,
            .rs1 = rs1,
            .rs2 = rs2,
            .funct7 = funct7,
            .imm = imm,
        };
    }

    /// Encode instruction back to 32-bit word (for testing round-trip)
    pub fn encode(self: Instruction) u32 {
        var word: u32 = 0;

        // Opcode [6:0]
        word |= @intFromEnum(self.opcode);

        // rd [11:7]
        word |= @as(u32, self.rd) << 7;

        // funct3 [14:12]
        word |= @as(u32, self.funct3) << 12;

        // rs1 [19:15]
        word |= @as(u32, self.rs1) << 15;

        // rs2/imm[4:0] [24:20]
        word |= @as(u32, self.rs2) << 20;

        // funct7/imm[11:5] [31:25]
        word |= @as(u32, self.funct7) << 25;

        return word;
    }

    /// Get a human-readable name for this instruction
    pub fn name(self: Instruction) []const u8 {
        return switch (self.opcode) {
            .OP => switch (self.funct3) {
                0b000 => if (self.funct7 == @intFromEnum(Funct7.NORM)) "add" else "sub",
                0b001 => "sll",
                0b010 => "slt",
                0b011 => "sltu",
                0b100 => "xor",
                0b101 => if (self.funct7 == @intFromEnum(Funct7.NORM)) "srl" else "sra",
                0b110 => "or",
                0b111 => "and",
            },
            .OP_IMM => switch (self.funct3) {
                0b000 => "addi",
                0b001 => "slli",
                0b010 => "slti",
                0b011 => "sltiu",
                0b100 => "xori",
                0b101 => if (self.funct7 == @intFromEnum(Funct7.NORM)) "srli" else "srai",
                0b110 => "ori",
                0b111 => "andi",
            },
            .LOAD => switch (self.funct3) {
                0b000 => "lb",
                0b001 => "lh",
                0b010 => "lw",
                0b100 => "lbu",
                0b101 => "lhu",
                else => "load?",
            },
            .STORE => switch (self.funct3) {
                0b000 => "sb",
                0b001 => "sh",
                0b010 => "sw",
                else => "store?",
            },
            .BRANCH => switch (self.funct3) {
                0b000 => "beq",
                0b001 => "bne",
                0b100 => "blt",
                0b101 => "bge",
                0b110 => "bltu",
                0b111 => "bgeu",
                else => "branch?",
            },
            .LUI => "lui",
            .AUIPC => "auipc",
            .JAL => "jal",
            .JALR => "jalr",
            .SYSTEM => "ecall/ebreak",
            else => "unknown",
        };
    }
};

/// Decode immediate value based on instruction format
fn decodeImmediate(word: u32, format: InstructionFormat) i32 {
    return switch (format) {
        // I-type: imm[11:0] = inst[31:20]
        .I => blk: {
            const imm_unsigned = (word >> 20) & 0xFFF;
            // Sign extend from bit 11
            const imm_signed = if ((imm_unsigned & 0x800) != 0)
                @as(i32, @intCast(imm_unsigned | 0xFFFFF000))
            else
                @as(i32, @intCast(imm_unsigned));
            break :blk imm_signed;
        },

        // S-type: imm[11:0] = {inst[31:25], inst[11:7]}
        .S => blk: {
            const imm_11_5 = (word >> 25) & 0x7F;
            const imm_4_0 = (word >> 7) & 0x1F;
            const imm_unsigned = (imm_11_5 << 5) | imm_4_0;
            // Sign extend from bit 11
            const imm_signed = if ((imm_unsigned & 0x800) != 0)
                @as(i32, @intCast(imm_unsigned | 0xFFFFF000))
            else
                @as(i32, @intCast(imm_unsigned));
            break :blk imm_signed;
        },

        // B-type: imm[12:1] = {inst[31], inst[7], inst[30:25], inst[11:8]}
        .B => blk: {
            const imm_12 = (word >> 31) & 0x1;
            const imm_11 = (word >> 7) & 0x1;
            const imm_10_5 = (word >> 25) & 0x3F;
            const imm_4_1 = (word >> 8) & 0xF;
            const imm_unsigned = (imm_12 << 12) | (imm_11 << 11) |
                (imm_10_5 << 5) | (imm_4_1 << 1);
            // Sign extend from bit 12
            const imm_signed = if ((imm_unsigned & 0x1000) != 0)
                @as(i32, @intCast(imm_unsigned | 0xFFFFE000))
            else
                @as(i32, @intCast(imm_unsigned));
            break :blk imm_signed;
        },

        // U-type: imm[31:12] = inst[31:12]
        .U => blk: {
            const imm_unsigned = word & 0xFFFFF000;
            break :blk @as(i32, @bitCast(imm_unsigned));
        },

        // J-type: imm[20:1] = {inst[31], inst[19:12], inst[20], inst[30:21]}
        .J => blk: {
            const imm_20 = (word >> 31) & 0x1;
            const imm_19_12 = (word >> 12) & 0xFF;
            const imm_11 = (word >> 20) & 0x1;
            const imm_10_1 = (word >> 21) & 0x3FF;
            const imm_unsigned = (imm_20 << 20) | (imm_19_12 << 12) |
                (imm_11 << 11) | (imm_10_1 << 1);
            // Sign extend from bit 20
            const imm_signed = if ((imm_unsigned & 0x100000) != 0)
                @as(i32, @intCast(imm_unsigned | 0xFFE00000))
            else
                @as(i32, @intCast(imm_unsigned));
            break :blk imm_signed;
        },

        // R-type: No immediate
        .R => 0,
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "rv32i: decode ADD instruction" {
    // add x1, x2, x3
    // R-type: opcode=0110011, rd=1, funct3=000, rs1=2, rs2=3, funct7=0000000
    const word: u32 = 0b0000000_00011_00010_000_00001_0110011;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.OP, inst.opcode);
    try testing.expectEqual(InstructionFormat.R, inst.format);
    try testing.expectEqual(@as(u5, 1), inst.rd);
    try testing.expectEqual(@as(u5, 2), inst.rs1);
    try testing.expectEqual(@as(u5, 3), inst.rs2);
    try testing.expectEqual(@as(u3, 0), inst.funct3);
    try testing.expectEqual(@as(u7, 0), inst.funct7);
    try testing.expectEqualStrings("add", inst.name());
}

test "rv32i: decode ADDI instruction" {
    // addi x1, x2, 42
    // I-type: opcode=0010011, rd=1, funct3=000, rs1=2, imm=42
    const word: u32 = 0b000000101010_00010_000_00001_0010011;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.OP_IMM, inst.opcode);
    try testing.expectEqual(InstructionFormat.I, inst.format);
    try testing.expectEqual(@as(u5, 1), inst.rd);
    try testing.expectEqual(@as(u5, 2), inst.rs1);
    try testing.expectEqual(@as(i32, 42), inst.imm);
    try testing.expectEqualStrings("addi", inst.name());
}

test "rv32i: decode LW instruction" {
    // lw x1, 4(x2)
    // I-type: opcode=0000011, rd=1, funct3=010, rs1=2, imm=4
    const word: u32 = 0b000000000100_00010_010_00001_0000011;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.LOAD, inst.opcode);
    try testing.expectEqual(@as(i32, 4), inst.imm);
    try testing.expectEqualStrings("lw", inst.name());
}

test "rv32i: decode SW instruction" {
    // sw x3, 8(x2)
    // S-type: opcode=0100011, funct3=010, rs1=2, rs2=3, imm=8
    const imm_11_5: u32 = 0b0000000;
    const imm_4_0: u32 = 0b01000;
    const word: u32 = (imm_11_5 << 25) | (3 << 20) | (2 << 15) |
        (0b010 << 12) | (imm_4_0 << 7) | 0b0100011;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.STORE, inst.opcode);
    try testing.expectEqual(InstructionFormat.S, inst.format);
    try testing.expectEqual(@as(i32, 8), inst.imm);
    try testing.expectEqualStrings("sw", inst.name());
}

test "rv32i: decode BEQ instruction" {
    // beq x1, x2, 8
    // B-type: opcode=1100011, funct3=000, rs1=1, rs2=2, imm=8
    const word: u32 = 0b0_000000_00010_00001_000_0100_0_1100011;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.BRANCH, inst.opcode);
    try testing.expectEqual(InstructionFormat.B, inst.format);
    try testing.expectEqual(@as(i32, 8), inst.imm);
    try testing.expectEqualStrings("beq", inst.name());
}

test "rv32i: decode LUI instruction" {
    // lui x1, 0x12345
    // U-type: opcode=0110111, rd=1, imm=0x12345000
    const word: u32 = (0x12345 << 12) | (1 << 7) | 0b0110111;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.LUI, inst.opcode);
    try testing.expectEqual(InstructionFormat.U, inst.format);
    try testing.expectEqual(@as(i32, @bitCast(@as(u32, 0x12345000))), inst.imm);
    try testing.expectEqualStrings("lui", inst.name());
}

test "rv32i: decode JAL instruction" {
    // jal x1, 1024
    // J-type: opcode=1101111, rd=1, imm=1024
    const word: u32 = 0b0_0000000010_0_00000000_00001_1101111;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(Opcode.JAL, inst.opcode);
    try testing.expectEqual(InstructionFormat.J, inst.format);
    try testing.expectEqual(@as(i32, 1024), inst.imm);
    try testing.expectEqualStrings("jal", inst.name());
}

test "rv32i: sign extension for negative immediates" {
    // addi x1, x2, -1
    // I-type with imm = -1 (0xFFF in 12 bits)
    const word: u32 = 0b111111111111_00010_000_00001_0010011;

    const inst = try Instruction.decode(word);

    try testing.expectEqual(@as(i32, -1), inst.imm);
}

test "rv32i: round-trip encoding" {
    // add x5, x10, x15
    const original: u32 = 0b0000000_01111_01010_000_00101_0110011;

    const inst = try Instruction.decode(original);
    const encoded = inst.encode();

    try testing.expectEqual(original, encoded);
}
