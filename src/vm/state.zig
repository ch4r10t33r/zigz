const std = @import("std");
const rv64i = @import("../isa/rv64i.zig");
const RegisterFile = @import("registers.zig").RegisterFile;
const Memory = @import("memory.zig").Memory;
const LoadSize = @import("memory.zig").LoadSize;
const ExecutionTrace = @import("trace.zig").ExecutionTrace;
const Step = @import("trace.zig").Step;
const MemoryAccess = @import("trace.zig").MemoryAccess;
const AccessType = @import("trace.zig").AccessType;
const instruction_table = @import("../isa/instruction_table.zig");

/// RISC-V VM State Machine
///
/// Executes RISC-V RV64I instructions and records an execution trace
/// for zkSNARK proving. The VM maintains:
/// - 32 general-purpose 64-bit registers
/// - Sparse byte-addressable memory
/// - Program counter (PC)
/// - Execution trace for proving
///
/// The execution model is:
/// 1. Fetch instruction at PC
/// 2. Decode instruction
/// 3. Execute instruction (update registers/memory)
/// 4. Record state transition in trace
/// 5. Update PC (pc + 4 or branch target)
/// 6. Repeat

pub const VMState = struct {
    /// Program counter
    pc: u64,

    /// Register file (x0-x31)
    regs: RegisterFile,

    /// Memory
    memory: Memory,

    /// Execution trace
    trace: ExecutionTrace,

    /// Step counter
    step_count: usize,

    /// Halt flag (set by EBREAK or errors)
    halted: bool,

    /// Allocator
    allocator: std.mem.Allocator,

    const Self = @This();

    /// Initialize VM with program loaded at given address
    pub fn init(
        allocator: std.mem.Allocator,
        program: []const u8,
        start_pc: u64,
    ) !Self {
        var memory = Memory.init(allocator);
        try memory.loadProgram(start_pc, program);

        return Self{
            .pc = start_pc,
            .regs = RegisterFile.init(),
            .memory = memory,
            .trace = ExecutionTrace.init(allocator),
            .step_count = 0,
            .halted = false,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Self) void {
        self.memory.deinit();
        self.trace.deinit();
    }

    /// Execute a single instruction and record in trace
    pub fn step(self: *Self) !void {
        if (self.halted) return error.VMHalted;

        // Snapshot state before execution
        const regs_before = self.regs.snapshot();
        const pc_before = self.pc;

        // Fetch instruction
        const inst_word = self.memory.loadWord(self.pc);
        const inst = rv64i.Instruction.decode(inst_word) catch {
            self.halted = true;
            return error.InvalidInstruction;
        };

        // Execute instruction
        var memory_access: ?MemoryAccess = null;
        const next_pc = try self.execute(inst, &memory_access);

        // Snapshot state after execution
        const regs_after = self.regs.snapshot();

        // Get lookup table metadata
        const lookup = instruction_table.getTableMetadata(inst);

        // Record step in trace
        try self.trace.addStep(Step{
            .step_num = self.step_count,
            .pc = pc_before,
            .instruction = inst,
            .regs_before = regs_before,
            .regs_after = regs_after,
            .memory_access = memory_access,
            .next_pc = next_pc,
            .lookup_table = lookup,
        });

        // Update PC
        self.pc = next_pc;
        self.step_count += 1;
    }

    /// Run VM until halt or max steps reached
    pub fn run(self: *Self, max_steps: usize) !void {
        var steps: usize = 0;
        while (!self.halted and steps < max_steps) : (steps += 1) {
            try self.step();
        }

        if (steps >= max_steps and !self.halted) {
            return error.MaxStepsExceeded;
        }
    }

    /// Execute a single instruction
    /// Returns the next PC value
    fn execute(self: *Self, inst: rv64i.Instruction, mem_access: *?MemoryAccess) !u64 {
        return switch (inst.opcode) {
            .OP => try self.executeOP(inst),
            .OP_32 => try self.executeOP32(inst),
            .OP_IMM => try self.executeOPIMM(inst),
            .OP_IMM_32 => try self.executeOPIMM32(inst),
            .LOAD => try self.executeLOAD(inst, mem_access),
            .STORE => try self.executeSTORE(inst, mem_access),
            .BRANCH => try self.executeBRANCH(inst),
            .JAL => try self.executeJAL(inst),
            .JALR => try self.executeJALR(inst),
            .LUI => try self.executeLUI(inst),
            .AUIPC => try self.executeAUIPC(inst),
            .SYSTEM => try self.executeSYSTEM(inst),
            else => {
                std.debug.print("Unimplemented opcode: {}\n", .{inst.opcode});
                return error.UnimplementedInstruction;
            },
        };
    }

    // ========================================================================
    // Instruction Execution Functions
    // ========================================================================

    fn executeOP(self: *Self, inst: rv64i.Instruction) !u64 {
        const rs1_val = self.regs.read(inst.rs1);
        const rs2_val = self.regs.read(inst.rs2);

        const result = switch (inst.funct3) {
            0b000 => blk: { // ADD or SUB
                if (inst.funct7 == 0b0100000) {
                    break :blk rs1_val -% rs2_val; // SUB
                } else {
                    break :blk rs1_val +% rs2_val; // ADD
                }
            },
            0b001 => rs1_val << @truncate(rs2_val & 0x3F), // SLL (shift by low 6 bits)
            0b010 => @intFromBool(@as(i64, @bitCast(rs1_val)) < @as(i64, @bitCast(rs2_val))), // SLT (signed)
            0b011 => @intFromBool(rs1_val < rs2_val), // SLTU (unsigned)
            0b100 => rs1_val ^ rs2_val, // XOR
            0b101 => blk: { // SRL or SRA
                const shamt: u6 = @truncate(rs2_val & 0x3F);
                if (inst.funct7 == 0b0100000) {
                    // SRA (arithmetic right shift)
                    break :blk @as(u64, @bitCast(@as(i64, @bitCast(rs1_val)) >> shamt));
                } else {
                    // SRL (logical right shift)
                    break :blk rs1_val >> shamt;
                }
            },
            0b110 => rs1_val | rs2_val, // OR
            0b111 => rs1_val & rs2_val, // AND
        };

        self.regs.write(inst.rd, result);
        return self.pc + 4;
    }

    fn executeOP32(self: *Self, inst: rv64i.Instruction) !u64 {
        // RV64I: Word operations (operate on low 32 bits, sign-extend result)
        const rs1_val = @as(u32, @truncate(self.regs.read(inst.rs1)));
        const rs2_val = @as(u32, @truncate(self.regs.read(inst.rs2)));

        const result32 = switch (inst.funct3) {
            0b000 => blk: { // ADDW or SUBW
                if (inst.funct7 == 0b0100000) {
                    break :blk rs1_val -% rs2_val; // SUBW
                } else {
                    break :blk rs1_val +% rs2_val; // ADDW
                }
            },
            0b001 => rs1_val << @truncate(rs2_val & 0x1F), // SLLW
            0b101 => blk: { // SRLW or SRAW
                const shamt: u5 = @truncate(rs2_val & 0x1F);
                if (inst.funct7 == 0b0100000) {
                    break :blk @as(u32, @bitCast(@as(i32, @bitCast(rs1_val)) >> shamt)); // SRAW
                } else {
                    break :blk rs1_val >> shamt; // SRLW
                }
            },
            else => return error.InvalidOP32,
        };

        // Sign-extend 32-bit result to 64 bits
        const result64: u64 = @bitCast(@as(i64, @as(i32, @bitCast(result32))));
        self.regs.write(inst.rd, result64);
        return self.pc + 4;
    }

    fn executeOPIMM(self: *Self, inst: rv64i.Instruction) !u64 {
        const rs1_val = self.regs.read(inst.rs1);
        // Sign-extend i32 immediate to i64, then bitcast to u64
        const imm_i64: i64 = @intCast(inst.imm);
        const imm = @as(u64, @bitCast(imm_i64));

        const result = switch (inst.funct3) {
            0b000 => rs1_val +% imm, // ADDI
            0b001 => rs1_val << @truncate(imm & 0x3F), // SLLI
            0b010 => @intFromBool(@as(i64, @bitCast(rs1_val)) < inst.imm), // SLTI (signed)
            0b011 => @intFromBool(rs1_val < imm), // SLTIU (unsigned)
            0b100 => rs1_val ^ imm, // XORI
            0b101 => blk: { // SRLI or SRAI
                const shamt: u6 = @truncate(imm & 0x3F);
                if (inst.funct7 == 0b0100000) {
                    break :blk @as(u64, @bitCast(@as(i64, @bitCast(rs1_val)) >> shamt)); // SRAI
                } else {
                    break :blk rs1_val >> shamt; // SRLI
                }
            },
            0b110 => rs1_val | imm, // ORI
            0b111 => rs1_val & imm, // ANDI
        };

        self.regs.write(inst.rd, result);
        return self.pc + 4;
    }

    fn executeOPIMM32(self: *Self, inst: rv64i.Instruction) !u64 {
        // RV64I: Word immediate operations
        const rs1_val = @as(u32, @truncate(self.regs.read(inst.rs1)));
        const imm = @as(u32, @truncate(@as(u64, @bitCast(inst.imm))));

        const result32 = switch (inst.funct3) {
            0b000 => rs1_val +% imm, // ADDIW
            0b001 => rs1_val << @truncate(imm & 0x1F), // SLLIW
            0b101 => blk: { // SRLIW or SRAIW
                const shamt: u5 = @truncate(imm & 0x1F);
                if (inst.funct7 == 0b0100000) {
                    break :blk @as(u32, @bitCast(@as(i32, @bitCast(rs1_val)) >> shamt)); // SRAIW
                } else {
                    break :blk rs1_val >> shamt; // SRLIW
                }
            },
            else => return error.InvalidOPIMM32,
        };

        // Sign-extend to 64 bits
        const result64: u64 = @bitCast(@as(i64, @as(i32, @bitCast(result32))));
        self.regs.write(inst.rd, result64);
        return self.pc + 4;
    }

    fn executeLOAD(self: *Self, inst: rv64i.Instruction, mem_access: *?MemoryAccess) !u64 {
        const base = self.regs.read(inst.rs1);
        const addr = base +% @as(u64, @bitCast(inst.imm));

        const result: u64 = switch (inst.funct3) {
            0b000 => @bitCast(self.memory.loadSignExtended(addr, .Byte)), // LB
            0b001 => @bitCast(self.memory.loadSignExtended(addr, .Halfword)), // LH
            0b010 => @bitCast(self.memory.loadSignExtended(addr, .Word)), // LW
            0b011 => self.memory.loadDoubleword(addr), // LD (RV64I)
            0b100 => self.memory.loadZeroExtended(addr, .Byte), // LBU
            0b101 => self.memory.loadZeroExtended(addr, .Halfword), // LHU
            0b110 => self.memory.loadZeroExtended(addr, .Word), // LWU (RV64I)
            else => return error.InvalidLoadFunct3,
        };

        mem_access.* = MemoryAccess{
            .access_type = .Load,
            .address = addr,
            .value = result,
            .size = switch (inst.funct3) {
                0b000, 0b100 => .Byte,
                0b001, 0b101 => .Halfword,
                0b010, 0b110 => .Word,
                0b011 => .Doubleword,
                else => unreachable,
            },
        };

        self.regs.write(inst.rd, result);
        return self.pc + 4;
    }

    fn executeSTORE(self: *Self, inst: rv64i.Instruction, mem_access: *?MemoryAccess) !u64 {
        const base = self.regs.read(inst.rs1);
        const addr = base +% @as(u64, @bitCast(inst.imm));
        const value = self.regs.read(inst.rs2);

        const size: LoadSize = switch (inst.funct3) {
            0b000 => .Byte, // SB
            0b001 => .Halfword, // SH
            0b010 => .Word, // SW
            0b011 => .Doubleword, // SD (RV64I)
            else => return error.InvalidStoreFunct3,
        };

        try self.memory.store(addr, value, size);

        mem_access.* = MemoryAccess{
            .access_type = .Store,
            .address = addr,
            .value = value,
            .size = size,
        };

        return self.pc + 4;
    }

    fn executeBRANCH(self: *Self, inst: rv64i.Instruction) !u64 {
        const rs1_val = self.regs.read(inst.rs1);
        const rs2_val = self.regs.read(inst.rs2);

        const branch_taken = switch (inst.funct3) {
            0b000 => rs1_val == rs2_val, // BEQ
            0b001 => rs1_val != rs2_val, // BNE
            0b100 => @as(i64, @bitCast(rs1_val)) < @as(i64, @bitCast(rs2_val)), // BLT
            0b101 => @as(i64, @bitCast(rs1_val)) >= @as(i64, @bitCast(rs2_val)), // BGE
            0b110 => rs1_val < rs2_val, // BLTU
            0b111 => rs1_val >= rs2_val, // BGEU
            else => return error.InvalidBranchFunct3,
        };

        if (branch_taken) {
            return self.pc +% @as(u64, @bitCast(inst.imm));
        } else {
            return self.pc + 4;
        }
    }

    fn executeJAL(self: *Self, inst: rv64i.Instruction) !u64 {
        // Save return address
        self.regs.write(inst.rd, self.pc + 4);

        // Jump to target
        return self.pc +% @as(u64, @bitCast(inst.imm));
    }

    fn executeJALR(self: *Self, inst: rv64i.Instruction) !u64 {
        const base = self.regs.read(inst.rs1);

        // Save return address
        self.regs.write(inst.rd, self.pc + 4);

        // Jump to (base + imm) & ~1 (clear lowest bit)
        const target = (base +% @as(u64, @bitCast(inst.imm))) & ~@as(u64, 1);
        return target;
    }

    fn executeLUI(self: *Self, inst: rv64i.Instruction) !u64 {
        // Load Upper Immediate
        // LUI places the 20-bit immediate in bits [31:12] and zeros the lower 12 bits
        // Sign-extend to 64 bits for RV64I
        self.regs.write(inst.rd, @bitCast(inst.imm));
        return self.pc + 4;
    }

    fn executeAUIPC(self: *Self, inst: rv64i.Instruction) !u64 {
        // Add Upper Immediate to PC
        const result = self.pc +% @as(u64, @bitCast(inst.imm));
        self.regs.write(inst.rd, result);
        return self.pc + 4;
    }

    fn executeSYSTEM(self: *Self, inst: rv64i.Instruction) !u64 {
        // SYSTEM instructions include ECALL, EBREAK, CSR operations
        if (inst.funct3 == 0) {
            if (inst.imm == 0) {
                // ECALL - Environment call (syscall)
                // For now, we'll just continue execution
                // In a full implementation, this would trigger syscall handling
                return self.pc + 4;
            } else if (inst.imm == 1) {
                // EBREAK - Debugger breakpoint / halt
                self.halted = true;
                return self.pc;
            }
        }

        // CSR operations not yet implemented
        return error.UnimplementedSYSTEM;
    }
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "vm: execute ADDI instruction" {
    // ADDI x10, x0, 42
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x02, // ADDI x10, x0, 42 (little endian)
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.step();

    // x10 should now contain 42
    try testing.expectEqual(@as(u64, 42), vm.regs.read(10));
    try testing.expectEqual(@as(u64, 0x1004), vm.pc);
    try testing.expectEqual(@as(usize, 1), vm.step_count);
}

test "vm: execute ADD instruction" {
    // ADDI x10, x0, 10
    // ADDI x11, x0, 20
    // ADD x12, x10, x11
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x00, // ADDI x10, x0, 10
        0x93, 0x05, 0x40, 0x01, // ADDI x11, x0, 20
        0x33, 0x06, 0xB5, 0x00, // ADD x12, x10, x11
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 10), vm.regs.read(10));
    try testing.expectEqual(@as(u64, 20), vm.regs.read(11));
    try testing.expectEqual(@as(u64, 30), vm.regs.read(12));
}

test "vm: execute LW/SW instructions" {
    // ADDI x10, x0, 100    # x10 = 100
    // SW x10, 0(x0)        # mem[0] = 100
    // LW x11, 0(x0)        # x11 = mem[0]
    const program = [_]u8{
        0x13, 0x05, 0x40, 0x06, // ADDI x10, x0, 100
        0x23, 0x20, 0xA0, 0x00, // SW x10, 0(x0)
        0x83, 0x25, 0x00, 0x00, // LW x11, 0(x0)
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    try testing.expectEqual(@as(u64, 100), vm.regs.read(11));
}

test "vm: execute BEQ branch" {
    // ADDI x10, x0, 5
    // ADDI x11, x0, 5
    // BEQ x10, x11, 8   # Skip next instruction if equal
    // ADDI x12, x0, 99  # This should be skipped
    // ADDI x13, x0, 42  # This should execute
    const program = [_]u8{
        0x13, 0x05, 0x50, 0x00, // ADDI x10, x0, 5
        0x93, 0x05, 0x50, 0x00, // ADDI x11, x0, 5
        0x63, 0x04, 0xB5, 0x00, // BEQ x10, x11, 8
        0x13, 0x06, 0x30, 0x06, // ADDI x12, x0, 99
        0x93, 0x06, 0xA0, 0x02, // ADDI x13, x0, 42
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(10);

    try testing.expectEqual(@as(u64, 0), vm.regs.read(12)); // Should be skipped
    try testing.expectEqual(@as(u64, 42), vm.regs.read(13)); // Should execute
}

test "vm: trace records all steps" {
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x02, // ADDI x10, x0, 42
        0x93, 0x05, 0xB0, 0x03, // ADDI x11, x0, 59
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(2);

    try testing.expectEqual(@as(usize, 2), vm.trace.stepCount());

    const stats = vm.trace.stats();
    try testing.expectEqual(@as(usize, 2), stats.total_steps);
}
