const std = @import("std");
const rv32i = @import("rv32i.zig");

/// Instruction Lookup Table Metadata
///
/// This module defines metadata for building lookup tables used in the
/// Lasso lookup argument (Phase 5). Each instruction's semantics can be
/// represented as a lookup table: (inputs) → (outputs).
///
/// For example:
/// - ADD: (rs1_val, rs2_val) → (rd_val)
/// - LW: (rs1_val, offset) → (mem_data, rd_val)
///
/// Large tables (32-bit × 32-bit) are decomposed into smaller subtables
/// using Lasso's digit-wise decomposition.

/// Lookup table structure for an instruction
///
/// Defines the shape and size of the lookup table needed
pub const LookupTable = struct {
    /// Instruction name
    name: []const u8,

    /// Number of input fields
    num_inputs: usize,

    /// Number of output fields
    num_outputs: usize,

    /// Input field widths (in bits)
    input_widths: []const usize,

    /// Output field widths (in bits)
    output_widths: []const usize,

    /// Total table size (product of input domains)
    table_size: usize,

    /// Whether this table needs decomposition (size > threshold)
    needs_decomposition: bool,

    /// Recommended decomposition strategy
    decomposition: ?DecompositionStrategy,

    /// Compute the total table size
    pub fn computeSize(input_widths: []const usize) usize {
        var size: usize = 1;
        for (input_widths) |width| {
            size *= (@as(usize, 1) << @intCast(width));
        }
        return size;
    }

    /// Check if table is feasible without decomposition
    /// Threshold: 2^24 entries (~16M entries, ~256MB for 64-bit fields)
    pub fn isFeasible(table_size: usize) bool {
        return table_size <= (1 << 24);
    }
};

/// Decomposition strategies for large lookup tables
pub const DecompositionStrategy = enum {
    /// Decompose into 16-bit chunks
    /// Example: 32-bit × 32-bit → multiple 16-bit × 16-bit
    Chunk16,

    /// Decompose into 8-bit chunks
    /// Example: 32-bit → four 8-bit lookups
    Chunk8,

    /// Sparse table (only store non-zero entries)
    Sparse,

    /// Procedural generation (compute on-the-fly)
    Procedural,
};

/// RV32I instruction lookup table catalog
///
/// Defines the lookup table structure for each RV32I instruction
pub const InstructionTables = struct {
    /// Arithmetic instructions (R-type and I-type)
    pub const ADD = LookupTable{
        .name = "ADD",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }), // 2^64 entries!
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    pub const SUB = LookupTable{
        .name = "SUB",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    pub const AND = LookupTable{
        .name = "AND",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk8, // Bitwise ops work well with byte chunks
    };

    pub const OR = LookupTable{
        .name = "OR",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk8,
    };

    pub const XOR = LookupTable{
        .name = "XOR",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk8,
    };

    /// Shift instructions (amount is only 5 bits)
    pub const SLL = LookupTable{
        .name = "SLL",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 5 }, // value, shift_amount
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 5 }), // 2^37 entries
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    pub const SRL = LookupTable{
        .name = "SRL",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 5 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 5 }),
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    pub const SRA = LookupTable{
        .name = "SRA",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 5 },
        .output_widths = &[_]usize{32},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 5 }),
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    /// Comparison instructions (output is 1 bit)
    pub const SLT = LookupTable{
        .name = "SLT",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{1}, // Boolean result
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    pub const SLTU = LookupTable{
        .name = "SLTU",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{1},
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    /// Branch conditions (output is 1 bit)
    pub const BEQ = LookupTable{
        .name = "BEQ",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 },
        .output_widths = &[_]usize{1}, // Branch taken?
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Chunk16,
    };

    /// Load/Store (memory lookups handled separately)
    /// These interact with memory state, so they're more complex
    pub const LOAD = LookupTable{
        .name = "LOAD",
        .num_inputs = 2,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32 }, // address, mem_data
        .output_widths = &[_]usize{32}, // loaded value
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32 }),
        .needs_decomposition = true,
        .decomposition = .Sparse, // Memory is sparse!
    };

    pub const STORE = LookupTable{
        .name = "STORE",
        .num_inputs = 3,
        .num_outputs = 1,
        .input_widths = &[_]usize{ 32, 32, 32 }, // address, data, old_mem
        .output_widths = &[_]usize{32}, // new_mem
        .table_size = LookupTable.computeSize(&[_]usize{ 32, 32, 32 }), // 2^96!
        .needs_decomposition = true,
        .decomposition = .Sparse,
    };
};

/// Get lookup table metadata for an instruction
pub fn getTableMetadata(inst: rv32i.Instruction) ?LookupTable {
    return switch (inst.opcode) {
        .OP => switch (inst.funct3) {
            0b000 => if (inst.funct7 == 0) InstructionTables.ADD else InstructionTables.SUB,
            0b001 => InstructionTables.SLL,
            0b010 => InstructionTables.SLT,
            0b011 => InstructionTables.SLTU,
            0b100 => InstructionTables.XOR,
            0b101 => if (inst.funct7 == 0) InstructionTables.SRL else InstructionTables.SRA,
            0b110 => InstructionTables.OR,
            0b111 => InstructionTables.AND,
        },
        .OP_IMM => switch (inst.funct3) {
            0b000 => InstructionTables.ADD, // ADDI uses same table as ADD
            0b001 => InstructionTables.SLL, // SLLI
            0b010 => InstructionTables.SLT, // SLTI
            0b011 => InstructionTables.SLTU, // SLTIU
            0b100 => InstructionTables.XOR, // XORI
            0b101 => if (inst.funct7 == 0) InstructionTables.SRL else InstructionTables.SRA,
            0b110 => InstructionTables.OR, // ORI
            0b111 => InstructionTables.AND, // ANDI
        },
        .LOAD => InstructionTables.LOAD,
        .STORE => InstructionTables.STORE,
        .BRANCH => switch (inst.funct3) {
            0b000 => InstructionTables.BEQ, // BEQ
            // Other branches use similar tables
            else => InstructionTables.BEQ,
        },
        else => null,
    };
}

/// Estimate memory usage for a lookup table
pub fn estimateMemoryUsage(table: LookupTable, bytes_per_entry: usize) usize {
    if (table.needs_decomposition) {
        // Rough estimate for decomposed table
        return switch (table.decomposition.?) {
            .Chunk16 => {
                // 32-bit = two 16-bit chunks
                // Each chunk: 2^16 × 2^16 = 2^32 entries
                const chunk_size = (@as(usize, 1) << 32);
                return chunk_size * bytes_per_entry * 2;
            },
            .Chunk8 => {
                // 32-bit = four 8-bit chunks
                // Each chunk: 2^8 × 2^8 = 2^16 entries
                const chunk_size = (@as(usize, 1) << 16);
                return chunk_size * bytes_per_entry * 4;
            },
            .Sparse => {
                // Assume 1% occupancy for memory operations
                return (table.table_size / 100) * bytes_per_entry;
            },
            .Procedural => 0, // No storage needed
        };
    } else {
        return table.table_size * bytes_per_entry;
    }
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "instruction_table: ADD metadata" {
    const add_table = InstructionTables.ADD;

    try testing.expectEqual(@as(usize, 2), add_table.num_inputs);
    try testing.expectEqual(@as(usize, 1), add_table.num_outputs);
    try testing.expect(add_table.needs_decomposition);
    try testing.expectEqual(DecompositionStrategy.Chunk16, add_table.decomposition.?);
}

test "instruction_table: shift instruction smaller table" {
    const sll_table = InstructionTables.SLL;

    // Shift amount is only 5 bits, so table is smaller
    try testing.expectEqual(@as(usize, 32), sll_table.input_widths[0]);
    try testing.expectEqual(@as(usize, 5), sll_table.input_widths[1]);
    try testing.expect(sll_table.needs_decomposition);
}

test "instruction_table: comparison output is boolean" {
    const slt_table = InstructionTables.SLT;

    try testing.expectEqual(@as(usize, 1), slt_table.output_widths[0]);
}

test "instruction_table: memory usage estimation" {
    const add_table = InstructionTables.ADD;

    // Assuming 8 bytes per entry
    const mem_usage = estimateMemoryUsage(add_table, 8);

    // Should be feasible with decomposition
    try testing.expect(mem_usage < (1 << 30)); // < 1GB
}

test "instruction_table: get metadata for instruction" {
    // Decode an ADD instruction
    const word: u32 = 0b0000000_00011_00010_000_00001_0110011;
    const inst = try rv32i.Instruction.decode(word);

    const table = getTableMetadata(inst);
    try testing.expect(table != null);
    try testing.expectEqualStrings("ADD", table.?.name);
}

test "instruction_table: feasibility check" {
    // Small table should be feasible
    try testing.expect(LookupTable.isFeasible(1 << 16)); // 64K entries

    // Huge table not feasible
    try testing.expect(!LookupTable.isFeasible(1 << 32)); // 4B entries
}
