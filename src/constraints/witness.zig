const std = @import("std");
const Multilinear = @import("../poly/multilinear.zig").Multilinear;
const ExecutionTrace = @import("../vm/trace.zig").ExecutionTrace;
const Step = @import("../vm/trace.zig").Step;

/// Witness Generator for zkSNARK Proving
///
/// Converts VM execution traces into polynomial witness data.
/// The witness consists of multilinear polynomials over the boolean hypercube
/// that encode the execution trace in a form suitable for constraint checking.
///
/// For a trace with N steps (N = 2^ν), we generate polynomials over ν variables:
/// - PC polynomial: encodes program counter at each step
/// - Register polynomials: encode register values (32 polynomials, one per register)
/// - Memory polynomials: encode memory state (sparse representation)
/// - Instruction polynomials: encode instruction data (opcode, funct3, funct7, etc.)
///
/// These polynomials are then used by the constraint system to prove correct execution.

pub const WitnessGenerator = struct {
    allocator: std.mem.Allocator,

    const Self = @This();

    pub fn init(allocator: std.mem.Allocator) Self {
        return Self{ .allocator = allocator };
    }

    /// Generate complete witness from execution trace
    pub fn generate(
        self: Self,
        comptime F: type,
        trace: ExecutionTrace,
    ) !Witness(F) {
        const num_steps = trace.stepCount();

        // Number of boolean hypercube variables needed
        // We need 2^ν ≥ num_steps, so ν = ceil(log2(num_steps))
        const num_vars = if (num_steps == 0)
            0
        else
            std.math.log2_int_ceil(usize, num_steps);

        // Pad to power of 2
        const padded_steps = @as(usize, 1) << @intCast(num_vars);

        // Generate polynomials
        const pc_poly = try self.generatePCPoly(F, trace, padded_steps);
        const reg_polys = try self.generateRegisterPolys(F, trace, padded_steps);
        const inst_poly = try self.generateInstructionPoly(F, trace, padded_steps);
        const mem_poly = try self.generateMemoryPoly(F, trace, padded_steps);

        return Witness(F){
            .num_vars = num_vars,
            .num_steps = num_steps,
            .pc = pc_poly,
            .registers = reg_polys,
            .instruction = inst_poly,
            .memory = mem_poly,
            .allocator = self.allocator,
        };
    }

    /// Generate PC (Program Counter) polynomial
    /// Maps step index → PC value at that step
    fn generatePCPoly(
        self: Self,
        comptime F: type,
        trace: ExecutionTrace,
        padded_steps: usize,
    ) !Multilinear(F) {
        var evaluations = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(evaluations);

        // Fill in actual PC values
        for (trace.steps.items, 0..) |step, i| {
            evaluations[i] = F.init(step.pc);
        }

        // Pad with zeros (or last PC value)
        const last_pc = if (trace.steps.items.len > 0)
            F.init(trace.steps.items[trace.steps.items.len - 1].pc)
        else
            F.zero();

        for (trace.steps.items.len..padded_steps) |i| {
            evaluations[i] = last_pc;
        }

        return Multilinear(F).init(self.allocator, evaluations);
    }

    /// Generate register polynomials (one polynomial per register)
    /// For register i: maps step index → value of register i after that step
    fn generateRegisterPolys(
        self: Self,
        comptime F: type,
        trace: ExecutionTrace,
        padded_steps: usize,
    ) !RegisterPolynomials(F) {
        var polys: [32]Multilinear(F) = undefined;

        // Generate polynomial for each register
        for (0..32) |reg_idx| {
            var evaluations = try self.allocator.alloc(F, padded_steps);
            errdefer self.allocator.free(evaluations);

            // Fill in actual register values (after each step)
            for (trace.steps.items, 0..) |step, i| {
                const reg_val = step.regs_after.read(@intCast(reg_idx));
                evaluations[i] = F.init(reg_val);
            }

            // Pad with last value
            const last_val = if (trace.steps.items.len > 0)
                F.init(trace.steps.items[trace.steps.items.len - 1].regs_after.read(@intCast(reg_idx)))
            else
                F.zero();

            for (trace.steps.items.len..padded_steps) |i| {
                evaluations[i] = last_val;
            }

            polys[reg_idx] = try Multilinear(F).init(self.allocator, evaluations);
        }

        return RegisterPolynomials(F){ .polys = polys };
    }

    /// Generate instruction polynomial
    /// Encodes instruction data: opcode, funct3, funct7, rd, rs1, rs2, imm
    fn generateInstructionPoly(
        self: Self,
        comptime F: type,
        trace: ExecutionTrace,
        padded_steps: usize,
    ) !InstructionPolynomial(F) {
        var opcode_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(opcode_evals);

        var funct3_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(funct3_evals);

        var funct7_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(funct7_evals);

        var rd_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(rd_evals);

        var rs1_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(rs1_evals);

        var rs2_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(rs2_evals);

        var imm_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(imm_evals);

        // Fill in instruction data
        for (trace.steps.items, 0..) |step, i| {
            const inst = step.instruction;
            opcode_evals[i] = F.init(@intFromEnum(inst.opcode));
            funct3_evals[i] = F.init(inst.funct3);
            funct7_evals[i] = F.init(inst.funct7);
            rd_evals[i] = F.init(inst.rd);
            rs1_evals[i] = F.init(inst.rs1);
            rs2_evals[i] = F.init(inst.rs2);
            imm_evals[i] = F.init(@as(u64, @bitCast(@as(i64, inst.imm))));
        }

        // Pad with zeros
        for (trace.steps.items.len..padded_steps) |i| {
            opcode_evals[i] = F.zero();
            funct3_evals[i] = F.zero();
            funct7_evals[i] = F.zero();
            rd_evals[i] = F.zero();
            rs1_evals[i] = F.zero();
            rs2_evals[i] = F.zero();
            imm_evals[i] = F.zero();
        }

        return InstructionPolynomial(F){
            .opcode = try Multilinear(F).init(self.allocator, opcode_evals),
            .funct3 = try Multilinear(F).init(self.allocator, funct3_evals),
            .funct7 = try Multilinear(F).init(self.allocator, funct7_evals),
            .rd = try Multilinear(F).init(self.allocator, rd_evals),
            .rs1 = try Multilinear(F).init(self.allocator, rs1_evals),
            .rs2 = try Multilinear(F).init(self.allocator, rs2_evals),
            .imm = try Multilinear(F).init(self.allocator, imm_evals),
        };
    }

    /// Generate memory access polynomial
    /// Encodes memory operations: address, value, read/write
    fn generateMemoryPoly(
        self: Self,
        comptime F: type,
        trace: ExecutionTrace,
        padded_steps: usize,
    ) !MemoryPolynomial(F) {
        var addr_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(addr_evals);

        var value_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(value_evals);

        var is_read_evals = try self.allocator.alloc(F, padded_steps);
        errdefer self.allocator.free(is_read_evals);

        // Fill in memory access data
        for (trace.steps.items, 0..) |step, i| {
            if (step.memory_access) |mem_access| {
                addr_evals[i] = F.init(mem_access.address);
                value_evals[i] = F.init(mem_access.value);
                is_read_evals[i] = if (mem_access.access_type == .Load) F.one() else F.zero();
            } else {
                // No memory access in this step
                addr_evals[i] = F.zero();
                value_evals[i] = F.zero();
                is_read_evals[i] = F.zero();
            }
        }

        // Pad with zeros
        for (trace.steps.items.len..padded_steps) |i| {
            addr_evals[i] = F.zero();
            value_evals[i] = F.zero();
            is_read_evals[i] = F.zero();
        }

        return MemoryPolynomial(F){
            .address = try Multilinear(F).init(self.allocator, addr_evals),
            .value = try Multilinear(F).init(self.allocator, value_evals),
            .is_read = try Multilinear(F).init(self.allocator, is_read_evals),
        };
    }
};

/// Complete witness for a program execution
pub fn Witness(comptime F: type) type {
    return struct {
        /// Number of boolean hypercube variables (ν)
        num_vars: usize,

        /// Number of actual execution steps (may be < 2^ν due to padding)
        num_steps: usize,

        /// Program counter polynomial
        pc: Multilinear(F),

        /// Register polynomials (32 registers)
        registers: RegisterPolynomials(F),

        /// Instruction data polynomial
        instruction: InstructionPolynomial(F),

        /// Memory access polynomial
        memory: MemoryPolynomial(F),

        /// Allocator
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn deinit(self: *Self) void {
            self.pc.deinit();
            self.registers.deinit();
            self.instruction.deinit();
            self.memory.deinit();
        }

        /// Get total size of witness (in field elements)
        pub fn size(self: Self) usize {
            const domain_size = @as(usize, 1) << @intCast(self.num_vars);
            // PC + 32 registers + 7 instruction fields + 3 memory fields = 43 polynomials
            return domain_size * 43;
        }
    };
}

/// Register polynomials (one per register)
pub fn RegisterPolynomials(comptime F: type) type {
    return struct {
        polys: [32]Multilinear(F),

        const Self = @This();

        pub fn deinit(self: *Self) void {
            for (&self.polys) |*poly| {
                poly.deinit();
            }
        }

        pub fn get(self: Self, reg_idx: usize) Multilinear(F) {
            return self.polys[reg_idx];
        }
    };
}

/// Instruction polynomial (encodes instruction fields)
pub fn InstructionPolynomial(comptime F: type) type {
    return struct {
        opcode: Multilinear(F),
        funct3: Multilinear(F),
        funct7: Multilinear(F),
        rd: Multilinear(F),
        rs1: Multilinear(F),
        rs2: Multilinear(F),
        imm: Multilinear(F),

        const Self = @This();

        pub fn deinit(self: *Self) void {
            self.opcode.deinit();
            self.funct3.deinit();
            self.funct7.deinit();
            self.rd.deinit();
            self.rs1.deinit();
            self.rs2.deinit();
            self.imm.deinit();
        }
    };
}

/// Memory polynomial (encodes memory accesses)
pub fn MemoryPolynomial(comptime F: type) type {
    return struct {
        address: Multilinear(F),
        value: Multilinear(F),
        is_read: Multilinear(F), // 1 for read, 0 for write

        const Self = @This();

        pub fn deinit(self: *Self) void {
            self.address.deinit();
            self.value.deinit();
            self.is_read.deinit();
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const Goldilocks = @import("../core/field.zig").Goldilocks;
const VMState = @import("../vm/state.zig").VMState;

test "witness: generate from simple trace" {
    // Simple program: ADDI x10, x0, 42
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x02, // ADDI x10, x0, 42
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.step();

    const gen = WitnessGenerator.init(testing.allocator);
    var witness = try gen.generate(Goldilocks, vm.trace);
    defer witness.deinit();

    // Should have 1 variable (2^1 = 2 ≥ 1 step)
    try testing.expectEqual(@as(usize, 1), witness.num_vars);
    try testing.expectEqual(@as(usize, 1), witness.num_steps);

    // PC should be 0x1000 at step 0
    const pc_val = try witness.pc.eval(&[_]Goldilocks{Goldilocks.zero()});
    try testing.expect(pc_val.eql(Goldilocks.init(0x1000)));

    // x10 should be 42 after the step
    const x10_val = try witness.registers.get(10).eval(&[_]Goldilocks{Goldilocks.zero()});
    try testing.expect(x10_val.eql(Goldilocks.init(42)));
}

test "witness: multiple steps with padding" {
    // Program with 3 instructions
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x00, // ADDI x10, x0, 10
        0x93, 0x05, 0x40, 0x01, // ADDI x11, x0, 20
        0x33, 0x06, 0xB5, 0x00, // ADD x12, x10, x11
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    const gen = WitnessGenerator.init(testing.allocator);
    var witness = try gen.generate(Goldilocks, vm.trace);
    defer witness.deinit();

    // 3 steps → need 2 variables (2^2 = 4 ≥ 3)
    try testing.expectEqual(@as(usize, 2), witness.num_vars);
    try testing.expectEqual(@as(usize, 3), witness.num_steps);

    // Verify witness size
    const witness_size = witness.size();
    try testing.expectEqual(@as(usize, 4 * 43), witness_size); // 4 domain points × 43 polynomials
}

test "witness: memory access encoding" {
    // Program: ADDI x10, x0, 100; SW x10, 0(x0); LW x11, 0(x0)
    const program = [_]u8{
        0x13, 0x05, 0x40, 0x06, // ADDI x10, x0, 100
        0x23, 0x20, 0xA0, 0x00, // SW x10, 0(x0)
        0x83, 0x25, 0x00, 0x00, // LW x11, 0(x0)
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.run(3);

    const gen = WitnessGenerator.init(testing.allocator);
    var witness = try gen.generate(Goldilocks, vm.trace);
    defer witness.deinit();

    // Step 1 should have a store (is_read = 0)
    const point1 = [_]Goldilocks{ Goldilocks.zero(), Goldilocks.one() };
    const is_read1 = try witness.memory.is_read.eval(&point1);
    try testing.expect(is_read1.eql(Goldilocks.zero())); // Store

    // Step 2 should have a load (is_read = 1)
    const point2 = [_]Goldilocks{ Goldilocks.one(), Goldilocks.zero() };
    const is_read2 = try witness.memory.is_read.eval(&point2);
    try testing.expect(is_read2.eql(Goldilocks.one())); // Load
}
