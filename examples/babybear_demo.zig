const std = @import("std");
const zigz = @import("zigz");

// Import both fields for comparison
const BabyBear = zigz.BabyBear;
const Goldilocks = zigz.Goldilocks;
const VMState = zigz.VMState;
const WitnessGenerator = zigz.WitnessGenerator;
const ConstraintSystem = zigz.ConstraintSystem;
const Decompose64to31 = zigz.Decompose64to31;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    std.debug.print("\n=== BabyBear zkVM Demo ===\n\n", .{});

    // Simple RISC-V program: ADDI x10, x0, 42
    const program = [_]u8{
        0x13, 0x05, 0xA0, 0x02, // ADDI x10, x0, 42
    };

    // Execute the program
    var vm = try VMState.init(allocator, &program, 0x1000);
    defer vm.deinit();

    try vm.step();

    std.debug.print("Program executed: ADDI x10, x0, 42\n", .{});
    std.debug.print("x10 = {}\n\n", .{vm.regs.read(10)});

    // Generate witness with BabyBear field
    const gen = WitnessGenerator.init(allocator);

    var witness_bb = try gen.generate(BabyBear, vm.trace);
    defer witness_bb.deinit();

    std.debug.print("BabyBear Witness Generated:\n", .{});
    std.debug.print("  Field: BabyBear (p = 2^31 - 2^27 + 1 = {})\n", .{BabyBear.MODULUS});
    std.debug.print("  Num variables: {}\n", .{witness_bb.num_vars});
    std.debug.print("  Num steps: {}\n", .{witness_bb.num_steps});
    std.debug.print("  Witness size: {} field elements\n\n", .{witness_bb.size()});

    // Build constraint system
    var system_bb = ConstraintSystem.init(allocator);
    defer system_bb.deinit();

    try system_bb.build(BabyBear, witness_bb, vm.trace);

    const stats_bb = system_bb.stats();
    std.debug.print("BabyBear Constraint System:\n", .{});
    std.debug.print("  Total constraints: {}\n", .{stats_bb.total_constraints});
    std.debug.print("  Arithmetic constraints: {}\n", .{stats_bb.arithmetic_constraints});
    std.debug.print("  Lookup constraints: {}\n\n", .{stats_bb.lookup_constraints});

    // Demonstrate value decomposition for large values
    std.debug.print("=== Value Decomposition Demo ===\n\n", .{});

    const large_value: u64 = 0x123456789ABCDEF0;
    std.debug.print("Original 64-bit value: 0x{X}\n", .{large_value});

    // Decompose into 31-bit chunks
    const decomp = Decompose64to31.fromU64(large_value);
    std.debug.print("Decomposed into 31-bit chunks:\n", .{});
    std.debug.print("  Low (bits 0-30):   0x{X} ({})\n", .{ decomp.low, decomp.low });
    std.debug.print("  Middle (bits 31-61): 0x{X} ({})\n", .{ decomp.middle, decomp.middle });
    std.debug.print("  High (bits 62-63):  {} ({})\n", .{ decomp.high, decomp.high });

    // Reconstruct
    const reconstructed = decomp.toU64();
    std.debug.print("Reconstructed: 0x{X}\n", .{reconstructed});
    std.debug.print("Match: {}\n\n", .{reconstructed == large_value});

    // Convert to BabyBear field elements
    const field_elems = decomp.toFieldElements(BabyBear);
    std.debug.print("As BabyBear field elements:\n", .{});
    std.debug.print("  [0] = {} (< p = {})\n", .{ field_elems[0].value, BabyBear.MODULUS });
    std.debug.print("  [1] = {} (< p = {})\n", .{ field_elems[1].value, BabyBear.MODULUS });
    std.debug.print("  [2] = {} (< p = {})\n\n", .{ field_elems[2].value, BabyBear.MODULUS });

    // Compare field sizes
    std.debug.print("=== Field Comparison ===\n\n", .{});
    std.debug.print("BabyBear:   {} (~31 bits)\n", .{BabyBear.MODULUS});
    std.debug.print("Goldilocks: {} (~64 bits)\n", .{Goldilocks.MODULUS});
    std.debug.print("\nBabyBear advantages:\n", .{});
    std.debug.print("  - 2x better SIMD parallelism (8 vs 4 elements per AVX2 vector)\n", .{});
    std.debug.print("  - 2-4x faster field multiplication\n", .{});
    std.debug.print("  - Better cache utilization\n", .{});
    std.debug.print("  - Explicit value decomposition (clearer soundness)\n", .{});

    std.debug.print("\n=== Demo Complete ===\n", .{});
}
