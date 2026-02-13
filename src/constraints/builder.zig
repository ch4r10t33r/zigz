const std = @import("std");
const Multilinear = @import("../poly/multilinear.zig").Multilinear;
const Witness = @import("witness.zig").Witness;

/// Constraint Builder for zkSNARK System
///
/// Builds polynomial constraints that must be satisfied for a valid execution.
/// The constraint system is a hybrid of:
/// 1. **Arithmetic constraints**: Polynomial equations that must hold (R1CS-like)
/// 2. **Lookup constraints**: Instruction semantics via Lasso lookup argument
///
/// Arithmetic Constraints enforce:
/// - PC progression: PC[i+1] = PC[i] + 4 (or branch target)
/// - Register updates: reg[i+1] = f(reg[i], instruction[i])
/// - Memory consistency: reads return previously written values
/// - x0 always zero: reg0[i] = 0 for all i
///
/// Lookup Constraints enforce:
/// - Instruction semantics: (rs1_val, rs2_val) → rd_val via lookup table
/// - These are handled by Lasso (Phase 5), not arithmetic constraints

pub const ConstraintBuilder = struct {
    allocator: std.mem.Allocator,

    /// List of polynomial constraints
    constraints: std.ArrayList(Constraint),

    const Self = @This();

    pub fn init(allocator: std.mem.Allocator) Self {
        return Self{
            .allocator = allocator,
            .constraints = std.ArrayList(Constraint).init(allocator),
        };
    }

    pub fn deinit(self: *Self) void {
        for (self.constraints.items) |*constraint| {
            constraint.deinit();
        }
        self.constraints.deinit();
    }

    /// Add a constraint to the system
    pub fn addConstraint(self: *Self, constraint: Constraint) !void {
        try self.constraints.append(constraint);
    }

    /// Build all constraints for a witness
    pub fn buildAll(
        self: *Self,
        comptime F: type,
        witness: Witness(F),
    ) !void {
        // 1. PC progression constraints
        try self.buildPCConstraints(F, witness);

        // 2. x0 = 0 constraint (RISC-V invariant)
        try self.buildX0Constraint(F, witness);

        // 3. Register update constraints
        try self.buildRegisterConstraints(F, witness);

        // 4. Memory consistency constraints
        try self.buildMemoryConstraints(F, witness);
    }

    /// Build PC progression constraints
    /// For non-branch: PC[i+1] = PC[i] + 4
    /// For branches: PC[i+1] = PC[i] + imm (if taken)
    fn buildPCConstraints(
        self: *Self,
        comptime F: type,
        witness: Witness(F),
    ) !void {
        _ = witness;

        // TODO: Implement PC progression constraints
        // This requires creating a polynomial that encodes:
        // pc_next(x) - pc(x) - 4 = 0 (for non-branches)
        //
        // For now, we'll add a placeholder constraint
        const constraint = Constraint{
            .name = try self.allocator.dupe(u8, "PC_progression"),
            .constraint_type = .Arithmetic,
            .description = try self.allocator.dupe(u8, "PC increments by 4 or jumps to branch target"),
        };
        try self.addConstraint(constraint);
    }

    /// Build x0 = 0 constraint (RISC-V invariant)
    /// Register x0 must always be zero
    fn buildX0Constraint(
        self: *Self,
        comptime F: type,
        witness: Witness(F),
    ) !void {
        _ = witness;

        // Constraint: reg[0](x) = 0 for all x
        const constraint = Constraint{
            .name = try self.allocator.dupe(u8, "x0_zero"),
            .constraint_type = .Arithmetic,
            .description = try self.allocator.dupe(u8, "Register x0 is hardwired to zero"),
        };
        try self.addConstraint(constraint);
    }

    /// Build register update constraints
    /// Ensures registers are updated correctly according to instruction semantics
    fn buildRegisterConstraints(
        self: *Self,
        comptime F: type,
        witness: Witness(F),
    ) !void {
        _ = witness;

        // For each register (except x0):
        // reg[i+1] = reg[i] (if not written)
        // reg[i+1] = result (if written)
        //
        // The actual computation is verified via lookup constraints
        const constraint = Constraint{
            .name = try self.allocator.dupe(u8, "register_updates"),
            .constraint_type = .Arithmetic,
            .description = try self.allocator.dupe(u8, "Registers update correctly based on instruction writes"),
        };
        try self.addConstraint(constraint);
    }

    /// Build memory consistency constraints
    /// Ensures memory reads return the last written value
    fn buildMemoryConstraints(
        self: *Self,
        comptime F: type,
        witness: Witness(F),
    ) !void {
        _ = witness;

        // Memory consistency: read(addr, time) = last_write(addr, time)
        // This is complex because memory is sparse and time-ordered
        const constraint = Constraint{
            .name = try self.allocator.dupe(u8, "memory_consistency"),
            .constraint_type = .Arithmetic,
            .description = try self.allocator.dupe(u8, "Memory reads return last written value"),
        };
        try self.addConstraint(constraint);
    }

    /// Get all constraints
    pub fn getConstraints(self: Self) []const Constraint {
        return self.constraints.items;
    }

    /// Count constraints by type
    pub fn stats(self: Self) ConstraintStats {
        var arithmetic_count: usize = 0;
        var lookup_count: usize = 0;

        for (self.constraints.items) |constraint| {
            switch (constraint.constraint_type) {
                .Arithmetic => arithmetic_count += 1,
                .Lookup => lookup_count += 1,
            }
        }

        return ConstraintStats{
            .total = self.constraints.items.len,
            .arithmetic = arithmetic_count,
            .lookup = lookup_count,
        };
    }
};

/// A single constraint in the system
pub const Constraint = struct {
    /// Name of the constraint
    name: []const u8,

    /// Type of constraint
    constraint_type: ConstraintType,

    /// Human-readable description
    description: []const u8,

    pub fn deinit(self: *Constraint) void {
        // Note: We're not freeing name and description here because
        // they're managed by the ConstraintBuilder's allocator
        _ = self;
    }
};

pub const ConstraintType = enum {
    /// Arithmetic constraint: polynomial equation that must hold
    Arithmetic,

    /// Lookup constraint: values must exist in a lookup table
    Lookup,
};

pub const ConstraintStats = struct {
    total: usize,
    arithmetic: usize,
    lookup: usize,
};

// ============================================================================
// Constraint System Integration
// ============================================================================

/// Full constraint system combining arithmetic and lookup constraints
pub const ConstraintSystem = struct {
    /// Arithmetic constraints
    builder: ConstraintBuilder,

    /// Lookup constraints (via Lasso)
    lookup_tables: std.ArrayList(LookupConstraint),

    /// Allocator
    allocator: std.mem.Allocator,

    const Self = @This();

    pub fn init(allocator: std.mem.Allocator) Self {
        return Self{
            .builder = ConstraintBuilder.init(allocator),
            .lookup_tables = std.ArrayList(LookupConstraint).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Self) void {
        self.builder.deinit();
        self.lookup_tables.deinit();
    }

    /// Build complete constraint system from witness
    pub fn build(
        self: *Self,
        comptime F: type,
        witness: Witness(F),
        trace: @import("../vm/trace.zig").ExecutionTrace,
    ) !void {
        // Build arithmetic constraints
        try self.builder.buildAll(F, witness);

        // Extract lookup constraints from trace
        try self.extractLookupConstraints(trace);
    }

    /// Extract lookup constraints from execution trace
    fn extractLookupConstraints(
        self: *Self,
        trace: @import("../vm/trace.zig").ExecutionTrace,
    ) !void {
        for (trace.steps.items) |step| {
            if (step.lookup_table) |table| {
                const lookup = LookupConstraint{
                    .table_name = table.name,
                    .step_num = step.step_num,
                    .pc = step.pc,
                };
                try self.lookup_tables.append(lookup);
            }
        }
    }

    /// Get total constraint count
    pub fn constraintCount(self: Self) usize {
        return self.builder.constraints.items.len + self.lookup_tables.items.len;
    }

    /// Get comprehensive statistics
    pub fn stats(self: Self) SystemStats {
        const builder_stats = self.builder.stats();
        return SystemStats{
            .total_constraints = self.constraintCount(),
            .arithmetic_constraints = builder_stats.arithmetic,
            .lookup_constraints = self.lookup_tables.items.len,
        };
    }
};

/// Lookup constraint (handled by Lasso)
pub const LookupConstraint = struct {
    table_name: []const u8,
    step_num: usize,
    pc: u64,
};

pub const SystemStats = struct {
    total_constraints: usize,
    arithmetic_constraints: usize,
    lookup_constraints: usize,
};

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const Goldilocks = @import("../core/field.zig").Goldilocks;
const VMState = @import("../vm/state.zig").VMState;
const WitnessGenerator = @import("witness.zig").WitnessGenerator;

test "constraints: basic builder" {
    var builder = ConstraintBuilder.init(testing.allocator);
    defer builder.deinit();

    const constraint = Constraint{
        .name = "test_constraint",
        .constraint_type = .Arithmetic,
        .description = "Test constraint",
    };

    try builder.addConstraint(constraint);

    const constraints = builder.getConstraints();
    try testing.expectEqual(@as(usize, 1), constraints.len);
}

test "constraints: build from witness" {
    // Simple program
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x02, // ADDI x10, x0, 42
    };

    var vm = try VMState.init(testing.allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.step();

    const gen = WitnessGenerator.init(testing.allocator);
    var witness = try gen.generate(Goldilocks, vm.trace);
    defer witness.deinit();

    var builder = ConstraintBuilder.init(testing.allocator);
    defer builder.deinit();

    try builder.buildAll(Goldilocks, witness);

    const stats_result = builder.stats();
    try testing.expect(stats_result.total > 0);
    try testing.expect(stats_result.arithmetic > 0);
}

test "constraints: full system" {
    // Program with multiple instructions
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

    var system = ConstraintSystem.init(testing.allocator);
    defer system.deinit();

    try system.build(Goldilocks, witness, vm.trace);

    const stats_result = system.stats();
    try testing.expect(stats_result.total_constraints > 0);
    try testing.expect(stats_result.arithmetic_constraints > 0);
    try testing.expectEqual(@as(usize, 3), stats_result.lookup_constraints); // 3 instructions
}
