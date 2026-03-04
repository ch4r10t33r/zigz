const std = @import("std");

/// RISC-V RV64I Base Integer Instruction Set (64-bit)
///
/// RV64I extends RV32I to 64-bit address space and data registers.
/// Key differences from RV32I:
/// - Registers are 64 bits wide (XLEN=64)
/// - Adds doubleword (64-bit) load/store: LD, SD
/// - Adds word (32-bit) operations with sign extension: LWU, ADDIW, SLLIW, etc.
/// - The "*W" instructions operate on lower 32 bits and sign-extend the result
///
/// Reference: RISC-V Instruction Set Manual, Volume I: User-Level ISA
/// https://riscv.org/technical/specifications/

/// RISC-V instruction formats
///
/// RV64I uses the same 6 instruction formats as RV32I:
/// - R-type: Register-register operations
/// - I-type: Immediate operations
/// - S-type: Store operations
/// - B-type: Branch operations
/// - U-type: Upper immediate
/// - J-type: Jump
pub const InstructionFormat = enum {
    R, // Register-register
    I, // Immediate
    S, // Store
    B, // Branch
    U, // Upper immediate
    J, // Jump
};

/// RV64I Opcodes (bits [6:0])
///
/// Note: RV64I adds OP_IMM_32 and OP_32 opcodes for word operations
pub const Opcode = enum(u7) {
    LOAD = 0b0000011,      // LB, LH, LW, LD, LBU, LHU, LWU
    LOAD_FP = 0b0000111,   // FLW, FLD (floating-point, not implemented)
    MISC_MEM = 0b0001111,  // FENCE, FENCE.I
    OP_IMM = 0b0010011,    // ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI
    AUIPC = 0b0010111,     // AUIPC
    OP_IMM_32 = 0b0011011, // RV64I: ADDIW, SLLIW, SRLIW, SRAIW
    STORE = 0b0100011,     // SB, SH, SW, SD
    STORE_FP = 0b0100111,  // FSW, FSD (floating-point, not implemented)
    AMO = 0b0101111,       // Atomic operations (not implemented)
    OP = 0b0110011,        // ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
    LUI = 0b0110111,       // LUI
    OP_32 = 0b0111011,     // RV64I: ADDW, SUBW, SLLW, SRLW, SRAW
    MADD = 0b1000011,      // Floating-point multiply-add (not implemented)
    MSUB = 0b1000111,      // Floating-point multiply-sub (not implemented)
    NMSUB = 0b1001011,     // Floating-point negate multiply-sub (not implemented)
    NMADD = 0b1001111,     // Floating-point negate multiply-add (not implemented)
    OP_FP = 0b1010011,     // Floating-point operations (not implemented)
    BRANCH = 0b1100011,    // BEQ, BNE, BLT, BGE, BLTU, BGEU
    JALR = 0b1100111,      // JALR
    JAL = 0b1101111,       // JAL
    SYSTEM = 0b1110011,    // ECALL, EBREAK, CSR*

    _,                     // Catch-all for unknown opcodes

    /// Get the instruction format for this opcode
    pub fn instructionFormat(self: Opcode) InstructionFormat {
        return switch (self) {
            .OP, .OP_32, .AMO => .R,
            .OP_IMM, .OP_IMM_32, .JALR, .LOAD, .LOAD_FP, .MISC_MEM, .SYSTEM => .I,
            .STORE, .STORE_FP => .S,
            .BRANCH => .B,
            .LUI, .AUIPC => .U,
            .JAL => .J,
            .MADD, .MSUB, .NMSUB, .NMADD => .R, // R4-type (similar to R-type)
            .OP_FP => .R,
            _ => .R, // Unknown opcodes default to R-type
        };
    }
};

/// Funct3 field (bits [14:12])
///
/// Specifies the operation variant within an opcode class
pub const Funct3 = enum(u3) {
    // OP_IMM / OP
    ADD_SUB = 0b000, // ADDI/ADD/SUB
    SLL = 0b001,     // SLLI/SLL
    SLT = 0b010,     // SLTI/SLT
    SLTU = 0b011,    // SLTIU/SLTU
    XOR = 0b100,     // XORI/XOR
    SRL_SRA = 0b101, // SRLI/SRAI/SRL/SRA
    OR = 0b110,      // ORI/OR
    AND = 0b111,     // ANDI/AND

    // LOAD
    LB = 0b000,  // Load Byte (sign-extended)
    LH = 0b001,  // Load Halfword (sign-extended)
    LW = 0b010,  // Load Word (sign-extended in RV64I)
    LD = 0b011,  // Load Doubleword (RV64I only)
    LBU = 0b100, // Load Byte Unsigned
    LHU = 0b101, // Load Halfword Unsigned
    LWU = 0b110, // Load Word Unsigned (RV64I only)

    // STORE
    SB = 0b000, // Store Byte
    SH = 0b001, // Store Halfword
    SW = 0b010, // Store Word
    SD = 0b011, // Store Doubleword (RV64I only)

    // BRANCH
    BEQ = 0b000,  // Branch Equal
    BNE = 0b001,  // Branch Not Equal
    BLT = 0b100,  // Branch Less Than
    BGE = 0b101,  // Branch Greater or Equal
    BLTU = 0b110, // Branch Less Than Unsigned
    BGEU = 0b111, // Branch Greater or Equal Unsigned

    // MISC_MEM
    FENCE = 0b000,
    FENCE_I = 0b001,

    _,
};

/// Funct7 field (bits [31:25])
///
/// Provides additional encoding space for R-type instructions
pub const Funct7 = enum(u7) {
    NORMAL = 0b0000000, // Normal operations (ADD, SLL, SRL, etc.)
    ALT = 0b0100000,    // Alternative operations (SUB, SRA)
    _,
};

/// Decoded RISC-V instruction
///
/// All fields are present; irrelevant fields for a given format are zero
pub const Instruction = struct {
    opcode: Opcode,
    rd: u5,     // Destination register
    funct3: u3, // Function modifier
    rs1: u5,    // Source register 1
    rs2: u5,    // Source register 2
    funct7: u7, // Function modifier (R-type)
    imm: i64,   // Immediate value (64-bit for RV64I)

    /// Decode a 32-bit instruction word
    ///
    /// Returns the decoded instruction with all fields extracted.
    /// Immediate values are sign-extended to 64 bits.
    pub fn decode(inst: u32) !Instruction {
        // Extract opcode (bits [6:0])
        const opcode_bits = @as(u7, @truncate(inst & 0x7F));
        const opcode = @as(Opcode, @enumFromInt(opcode_bits));

        // Extract common fields
        const rd = @as(u5, @truncate((inst >> 7) & 0x1F));
        const funct3 = @as(u3, @truncate((inst >> 12) & 0x07));
        const rs1 = @as(u5, @truncate((inst >> 15) & 0x1F));
        const rs2 = @as(u5, @truncate((inst >> 20) & 0x1F));
        const funct7 = @as(u7, @truncate((inst >> 25) & 0x7F));

        // Decode immediate based on instruction format
        const format = opcode.instructionFormat();
        const imm = try decodeImmediate(inst, format);

        return Instruction{
            .opcode = opcode,
            .rd = rd,
            .funct3 = funct3,
            .rs1 = rs1,
            .rs2 = rs2,
            .funct7 = funct7,
            .imm = imm,
        };
    }

    /// Decode immediate value based on instruction format
    ///
    /// Sign-extends immediates to 64 bits for RV64I
    fn decodeImmediate(inst: u32, format: InstructionFormat) !i64 {
        return switch (format) {
            .I => blk: {
                // I-type: imm[11:0] = inst[31:20]
                const imm_unsigned = (inst >> 20) & 0xFFF;

                // Sign extend from bit 11 to 64 bits
                const imm32 = if ((imm_unsigned & 0x800) != 0)
                    @as(i32, @bitCast(imm_unsigned | 0xFFFFF000))
                else
                    @as(i32, @bitCast(imm_unsigned));

                break :blk @as(i64, imm32);
            },

            .S => blk: {
                // S-type: imm[11:0] = {inst[31:25], inst[11:7]}
                const imm_11_5 = (inst >> 25) & 0x7F;
                const imm_4_0 = (inst >> 7) & 0x1F;
                const imm_unsigned = (imm_11_5 << 5) | imm_4_0;

                // Sign extend from bit 11 to 64 bits
                const imm32 = if ((imm_unsigned & 0x800) != 0)
                    @as(i32, @bitCast(imm_unsigned | 0xFFFFF000))
                else
                    @as(i32, @bitCast(imm_unsigned));

                break :blk @as(i64, imm32);
            },

            .B => blk: {
                // B-type: imm[12:1] = {inst[31], inst[7], inst[30:25], inst[11:8]}
                const imm_12 = (inst >> 31) & 0x1;
                const imm_10_5 = (inst >> 25) & 0x3F;
                const imm_4_1 = (inst >> 8) & 0x0F;
                const imm_11 = (inst >> 7) & 0x1;

                const imm_unsigned = (imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1);

                // Sign extend from bit 12 to 64 bits
                const imm32 = if ((imm_unsigned & 0x1000) != 0)
                    @as(i32, @bitCast(imm_unsigned | 0xFFFFE000))
                else
                    @as(i32, @bitCast(imm_unsigned));

                break :blk @as(i64, imm32);
            },

            .U => blk: {
                // U-type: imm[31:12] = inst[31:12]
                const imm_unsigned = inst & 0xFFFFF000;

                // Sign extend to 64 bits
                const imm32 = @as(i32, @bitCast(imm_unsigned));
                break :blk @as(i64, imm32);
            },

            .J => blk: {
                // J-type: imm[20:1] = {inst[31], inst[19:12], inst[20], inst[30:21]}
                const imm_20 = (inst >> 31) & 0x1;
                const imm_10_1 = (inst >> 21) & 0x3FF;
                const imm_11 = (inst >> 20) & 0x1;
                const imm_19_12 = (inst >> 12) & 0xFF;

                const imm_unsigned = (imm_20 << 20) | (imm_19_12 << 12) | (imm_11 << 11) | (imm_10_1 << 1);

                // Sign extend from bit 20 to 64 bits
                const imm32 = if ((imm_unsigned & 0x100000) != 0)
                    @as(i32, @bitCast(imm_unsigned | 0xFFE00000))
                else
                    @as(i32, @bitCast(imm_unsigned));

                break :blk @as(i64, imm32);
            },

            .R => 0, // R-type has no immediate
        };
    }

    /// Check if this is an RV64I-specific instruction
    ///
    /// Returns true for instructions that are only in RV64I, not RV32I
    pub fn isRV64IOnly(self: Instruction) bool {
        return switch (self.opcode) {
            .OP_IMM_32, .OP_32 => true, // *W instructions
            .LOAD => self.funct3 == @intFromEnum(Funct3.LD) or
                self.funct3 == @intFromEnum(Funct3.LWU),
            .STORE => self.funct3 == @intFromEnum(Funct3.SD),
            else => false,
        };
    }

    /// Check if this instruction operates on 32-bit words (with sign extension)
    ///
    /// In RV64I, these instructions operate on the lower 32 bits and
    /// sign-extend the result to 64 bits
    pub fn isWordOperation(self: Instruction) bool {
        return switch (self.opcode) {
            .OP_IMM_32, .OP_32 => true,
            .LOAD => self.funct3 == @intFromEnum(Funct3.LW), // LW sign-extends in RV64I
            else => false,
        };
    }
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "rv64i: decode ADDI" {
    // ADDI x1, x2, 42
    // Format: I-type
    // imm[11:0] = 42 = 0x02A
    // rs1 = 2, rd = 1, funct3 = 0x0, opcode = 0x13
    const inst: u32 = (42 << 20) | (2 << 15) | (0 << 12) | (1 << 7) | 0x13;

    const decoded = try Instruction.decode(inst);

    try testing.expectEqual(Opcode.OP_IMM, decoded.opcode);
    try testing.expectEqual(@as(u5, 1), decoded.rd);
    try testing.expectEqual(@as(u5, 2), decoded.rs1);
    try testing.expectEqual(@as(i64, 42), decoded.imm);
    try testing.expect(!decoded.isRV64IOnly());
}

test "rv64i: decode ADDIW (RV64I-specific)" {
    // ADDIW x1, x2, 42
    // Format: I-type
    // imm[11:0] = 42
    // rs1 = 2, rd = 1, funct3 = 0x0, opcode = 0x1B (OP_IMM_32)
    const inst: u32 = (42 << 20) | (2 << 15) | (0 << 12) | (1 << 7) | 0x1B;

    const decoded = try Instruction.decode(inst);

    try testing.expectEqual(Opcode.OP_IMM_32, decoded.opcode);
    try testing.expectEqual(@as(u5, 1), decoded.rd);
    try testing.expectEqual(@as(u5, 2), decoded.rs1);
    try testing.expectEqual(@as(i64, 42), decoded.imm);
    try testing.expect(decoded.isRV64IOnly());
    try testing.expect(decoded.isWordOperation());
}

test "rv64i: decode LD (Load Doubleword)" {
    // LD x1, 8(x2)
    // Format: I-type
    // imm[11:0] = 8
    // rs1 = 2, rd = 1, funct3 = 0x3 (LD), opcode = 0x03
    const inst: u32 = (8 << 20) | (2 << 15) | (3 << 12) | (1 << 7) | 0x03;

    const decoded = try Instruction.decode(inst);

    try testing.expectEqual(Opcode.LOAD, decoded.opcode);
    try testing.expectEqual(@as(u3, @intFromEnum(Funct3.LD)), decoded.funct3);
    try testing.expectEqual(@as(u5, 1), decoded.rd);
    try testing.expectEqual(@as(u5, 2), decoded.rs1);
    try testing.expectEqual(@as(i64, 8), decoded.imm);
    try testing.expect(decoded.isRV64IOnly());
}

test "rv64i: decode SD (Store Doubleword)" {
    // SD x1, 16(x2)
    // Format: S-type
    // imm[11:5] = 0, imm[4:0] = 16
    // rs2 = 1, rs1 = 2, funct3 = 0x3 (SD), opcode = 0x23
    const imm_11_5 = (16 >> 5) & 0x7F;
    const imm_4_0 = 16 & 0x1F;
    const inst: u32 = (imm_11_5 << 25) | (1 << 20) | (2 << 15) | (3 << 12) | (imm_4_0 << 7) | 0x23;

    const decoded = try Instruction.decode(inst);

    try testing.expectEqual(Opcode.STORE, decoded.opcode);
    try testing.expectEqual(@as(u3, @intFromEnum(Funct3.SD)), decoded.funct3);
    try testing.expectEqual(@as(u5, 1), decoded.rs2);
    try testing.expectEqual(@as(u5, 2), decoded.rs1);
    try testing.expectEqual(@as(i64, 16), decoded.imm);
    try testing.expect(decoded.isRV64IOnly());
}

test "rv64i: decode LWU (Load Word Unsigned)" {
    // LWU x1, 4(x2)
    // Format: I-type
    // funct3 = 0x6 (LWU) - only in RV64I
    const inst: u32 = (4 << 20) | (2 << 15) | (6 << 12) | (1 << 7) | 0x03;

    const decoded = try Instruction.decode(inst);

    try testing.expectEqual(Opcode.LOAD, decoded.opcode);
    try testing.expectEqual(@as(u3, @intFromEnum(Funct3.LWU)), decoded.funct3);
    try testing.expect(decoded.isRV64IOnly());
}

test "rv64i: decode ADDW (Add Word)" {
    // ADDW x1, x2, x3
    // Format: R-type
    // opcode = 0x3B (OP_32), funct3 = 0x0, funct7 = 0x00
    const inst: u32 = (0 << 25) | (3 << 20) | (2 << 15) | (0 << 12) | (1 << 7) | 0x3B;

    const decoded = try Instruction.decode(inst);

    try testing.expectEqual(Opcode.OP_32, decoded.opcode);
    try testing.expectEqual(@as(u5, 1), decoded.rd);
    try testing.expectEqual(@as(u5, 2), decoded.rs1);
    try testing.expectEqual(@as(u5, 3), decoded.rs2);
    try testing.expect(decoded.isRV64IOnly());
    try testing.expect(decoded.isWordOperation());
}

test "rv64i: immediate sign extension to 64 bits" {
    // Test negative immediate (bit 11 set)
    // ADDI x1, x2, -1
    const imm_neg1: u32 = 0xFFF; // 12-bit representation of -1
    const inst: u32 = (imm_neg1 << 20) | (2 << 15) | (0 << 12) | (1 << 7) | 0x13;

    const decoded = try Instruction.decode(inst);

    // Should be sign-extended to -1 in 64 bits
    try testing.expectEqual(@as(i64, -1), decoded.imm);
}

test "rv64i: instruction format detection" {
    try testing.expectEqual(InstructionFormat.R, Opcode.OP.instructionFormat());
    try testing.expectEqual(InstructionFormat.R, Opcode.OP_32.instructionFormat());
    try testing.expectEqual(InstructionFormat.I, Opcode.OP_IMM.instructionFormat());
    try testing.expectEqual(InstructionFormat.I, Opcode.OP_IMM_32.instructionFormat());
    try testing.expectEqual(InstructionFormat.S, Opcode.STORE.instructionFormat());
    try testing.expectEqual(InstructionFormat.B, Opcode.BRANCH.instructionFormat());
    try testing.expectEqual(InstructionFormat.U, Opcode.LUI.instructionFormat());
    try testing.expectEqual(InstructionFormat.J, Opcode.JAL.instructionFormat());
}
