const std = @import("std");
const rv64i = @import("../isa/rv64i.zig");
const RegisterFile = @import("registers.zig").RegisterFile;
const Memory = @import("memory.zig").Memory;
const instruction_table = @import("../isa/instruction_table.zig");

/// Execution Trace for zkVM Proving
///
/// Records the complete execution history of the VM, including:
/// - All state transitions (PC, registers, memory)
/// - All instruction lookups
/// - All memory accesses
///
/// This trace is used to generate the zkSNARK proof that execution
/// was correct according to the RISC-V ISA semantics.

pub const ExecutionTrace = struct {
    /// Sequence of execution steps
    steps: std.ArrayList(Step),

    /// Allocator
    allocator: std.mem.Allocator,

    const Self = @This();

    pub fn init(allocator: std.mem.Allocator) Self {
        return Self{
            .steps = std.ArrayList(Step).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Self) void {
        self.steps.deinit();
    }

    /// Add a step to the trace
    pub fn addStep(self: *Self, step: Step) !void {
        try self.steps.append(step);
    }

    /// Get total number of steps executed
    pub fn stepCount(self: Self) usize {
        return self.steps.items.len;
    }

    /// Get statistics about the execution
    pub fn stats(self: Self) TraceStats {
        var instruction_counts = std.StringHashMap(usize).init(self.allocator);
        defer instruction_counts.deinit();

        var total_memory_accesses: usize = 0;

        for (self.steps.items) |step| {
            // Count instructions
            const inst_name = step.instruction.name();
            const count = instruction_counts.get(inst_name) orelse 0;
            instruction_counts.put(inst_name, count + 1) catch {};

            // Count memory accesses
            if (step.memory_access) |_| {
                total_memory_accesses += 1;
            }
        }

        return TraceStats{
            .total_steps = self.steps.items.len,
            .total_memory_accesses = total_memory_accesses,
        };
    }
};

/// A single execution step in the trace
pub const Step = struct {
    /// Step number (for debugging)
    step_num: usize,

    /// Program counter before this instruction
    pc: u64,

    /// The instruction executed
    instruction: rv64i.Instruction,

    /// Register state BEFORE executing this instruction
    regs_before: RegisterFile,

    /// Register state AFTER executing this instruction
    regs_after: RegisterFile,

    /// Memory access (if any)
    memory_access: ?MemoryAccess,

    /// Next PC (usually pc + 4, or branch target)
    next_pc: u64,

    /// Lookup table used for this instruction (for Lasso proving)
    lookup_table: ?instruction_table.LookupTable,
};

/// Record of a memory access
pub const MemoryAccess = struct {
    /// Type of access
    access_type: AccessType,

    /// Address accessed
    address: u64,

    /// Value read or written
    value: u64,

    /// Size of access
    size: @import("memory.zig").LoadSize,
};

pub const AccessType = enum {
    Load,
    Store,
};

/// Statistics about the execution trace
pub const TraceStats = struct {
    total_steps: usize,
    total_memory_accesses: usize,
};

// ============================================================================
// Trace Analysis Helpers
// ============================================================================

/// Extract all lookup table operations from the trace
/// This is used to generate Lasso proof inputs
pub fn extractLookups(
    trace: ExecutionTrace,
    allocator: std.mem.Allocator,
) !std.ArrayList(LookupOp) {
    var lookups = std.ArrayList(LookupOp).init(allocator);

    for (trace.steps.items) |step| {
        if (step.lookup_table) |table| {
            try lookups.append(LookupOp{
                .table = table,
                .step_num = step.step_num,
                .pc = step.pc,
            });
        }
    }

    return lookups;
}

/// A lookup operation extracted from the trace
pub const LookupOp = struct {
    table: instruction_table.LookupTable,
    step_num: usize,
    pc: u64,
};

/// Verify trace consistency (for debugging)
/// Ensures that:
/// - Each step's regs_after matches next step's regs_before
/// - PC progression is correct
pub fn verifyTraceConsistency(trace: ExecutionTrace) !void {
    if (trace.steps.items.len == 0) return;

    for (trace.steps.items[0 .. trace.steps.items.len - 1], 0..) |step, i| {
        const next_step = trace.steps.items[i + 1];

        // PC should progress correctly
        if (next_step.pc != step.next_pc) {
            std.debug.print("PC mismatch at step {}: next_pc={}, actual={}\n", .{
                i,
                step.next_pc,
                next_step.pc,
            });
            return error.TracePCMismatch;
        }

        // Register state should be consistent
        // (regs_after of step i should match regs_before of step i+1)
        for (0..32) |reg| {
            const val_after = step.regs_after.read(@intCast(reg));
            const val_before = next_step.regs_before.read(@intCast(reg));

            if (val_after != val_before) {
                std.debug.print("Register mismatch at step {}, reg {}: after={}, before={}\n", .{
                    i,
                    reg,
                    val_after,
                    val_before,
                });
                return error.TraceRegisterMismatch;
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "trace: basic trace creation" {
    var trace = ExecutionTrace.init(testing.allocator);
    defer trace.deinit();

    const regs = RegisterFile.init();

    const step = Step{
        .step_num = 0,
        .pc = 0x1000,
        .instruction = try rv64i.Instruction.decode(0b0000000_00011_00010_000_00001_0110011), // ADD
        .regs_before = regs,
        .regs_after = regs,
        .memory_access = null,
        .next_pc = 0x1004,
        .lookup_table = null,
    };

    try trace.addStep(step);

    try testing.expectEqual(@as(usize, 1), trace.stepCount());
}

test "trace: memory access recording" {
    var trace = ExecutionTrace.init(testing.allocator);
    defer trace.deinit();

    const regs = RegisterFile.init();

    const mem_access = MemoryAccess{
        .access_type = .Load,
        .address = 0x2000,
        .value = 0x42,
        .size = .Word,
    };

    const step = Step{
        .step_num = 0,
        .pc = 0x1000,
        .instruction = try rv64i.Instruction.decode(0b000000001000_00010_010_00001_0000011), // LW
        .regs_before = regs,
        .regs_after = regs,
        .memory_access = mem_access,
        .next_pc = 0x1004,
        .lookup_table = null,
    };

    try trace.addStep(step);

    const stats_ = trace.stats();
    try testing.expectEqual(@as(usize, 1), stats_.total_memory_accesses);
}

test "trace: lookup extraction" {
    var trace = ExecutionTrace.init(testing.allocator);
    defer trace.deinit();

    const regs = RegisterFile.init();

    const step = Step{
        .step_num = 0,
        .pc = 0x1000,
        .instruction = try rv64i.Instruction.decode(0b0000000_00011_00010_000_00001_0110011), // ADD
        .regs_before = regs,
        .regs_after = regs,
        .memory_access = null,
        .next_pc = 0x1004,
        .lookup_table = instruction_table.InstructionTables.ADD,
    };

    try trace.addStep(step);

    var lookups = try extractLookups(trace, testing.allocator);
    defer lookups.deinit();

    try testing.expectEqual(@as(usize, 1), lookups.items.len);
    try testing.expectEqualStrings("ADD", lookups.items[0].table.name);
}
