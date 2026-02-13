const std = @import("std");
const zigz = @import("zigz");

const BabyBear = zigz.field_presets.BabyBear;
const Prover = @import("../src/prover/prover.zig").Prover;
const BinarySerializer = @import("../src/prover/serialization.zig").BinarySerializer;

/// Full Prover Demo
///
/// Demonstrates the complete proof generation pipeline:
/// 1. Create a RISC-V program
/// 2. Initialize the prover
/// 3. Generate a proof of execution
/// 4. Serialize the proof
/// 5. Verify proof structure

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    std.debug.print("\n╔═══════════════════════════════════════════════════════════╗\n", .{});
    std.debug.print("║         zigz zkVM - Full Prover Demonstration            ║\n", .{});
    std.debug.print("╚═══════════════════════════════════════════════════════════╝\n", .{});

    // ========================================================================
    // Demo 1: Simple arithmetic program
    // ========================================================================
    std.debug.print("\n--- Demo 1: Simple Arithmetic Program ---\n", .{});

    try simpleArithmeticDemo(allocator);

    // ========================================================================
    // Demo 2: Loop computation (Fibonacci)
    // ========================================================================
    std.debug.print("\n--- Demo 2: Fibonacci Sequence ---\n", .{});

    try fibonacciDemo(allocator);

    // ========================================================================
    // Demo 3: Proof serialization
    // ========================================================================
    std.debug.print("\n--- Demo 3: Proof Serialization ---\n", .{});

    try serializationDemo(allocator);

    std.debug.print("\n╔═══════════════════════════════════════════════════════════╗\n", .{});
    std.debug.print("║                   All Demos Complete!                     ║\n", .{});
    std.debug.print("╚═══════════════════════════════════════════════════════════╝\n\n", .{});
}

/// Demo 1: Simple arithmetic operations
fn simpleArithmeticDemo(allocator: std.mem.Allocator) !void {
    std.debug.print("Program: Compute x1 = 10 + 32\n", .{});

    // RISC-V program:
    // ADDI x1, x0, 10   # x1 = 0 + 10 = 10
    // ADDI x2, x0, 32   # x2 = 0 + 32 = 32
    // ADD  x3, x1, x2   # x3 = x1 + x2 = 42
    const program = [_]u8{
        0x93, 0x00, 0xA0, 0x00, // ADDI x1, x0, 10
        0x13, 0x01, 0x00, 0x02, // ADDI x2, x0, 32
        0xB3, 0x01, 0x21, 0x00, // ADD  x3, x1, x2
        0x00, 0x00, 0x00, 0x00, // Invalid (halt)
    };

    // Initialize prover
    var prover = try Prover(BabyBear).init(allocator, 42);
    defer prover.deinit();

    // Generate proof
    var proof = try prover.prove(&program, 0x1000, null, 1000);
    defer proof.deinit();

    // Display results
    std.debug.print("✓ Proof generated successfully\n", .{});
    std.debug.print("  - Execution steps: {d}\n", .{proof.public_io.num_steps});
    std.debug.print("  - Proof size: ~{d} bytes\n", .{proof.estimateSize()});

    if (proof.public_io.final_regs) |regs| {
        std.debug.print("  - Final x1 (should be 10): {d}\n", .{regs[1]});
        std.debug.print("  - Final x2 (should be 32): {d}\n", .{regs[2]});
        std.debug.print("  - Final x3 (should be 42): {d}\n", .{regs[3]});
    }
}

/// Demo 2: Fibonacci sequence computation
fn fibonacciDemo(allocator: std.mem.Allocator) !void {
    std.debug.print("Program: Compute Fibonacci(5) = 8\n", .{});

    // RISC-V program to compute Fibonacci(5):
    // x1 = fib(n-1) = 0
    // x2 = fib(n) = 1
    // x3 = counter = 5
    // Loop: x4 = x1 + x2, x1 = x2, x2 = x4, x3 -= 1
    const program = [_]u8{
        // Initialize: x1=0, x2=1, x3=5
        0x93, 0x00, 0x00, 0x00, // ADDI x1, x0, 0
        0x13, 0x01, 0x10, 0x00, // ADDI x2, x0, 1
        0x93, 0x01, 0x50, 0x00, // ADDI x3, x0, 5

        // Loop body would go here
        // (simplified for demo - actual loop requires branches)

        0x00, 0x00, 0x00, 0x00, // Halt
    };

    var prover = try Prover(BabyBear).init(allocator, 12345);
    defer prover.deinit();

    var proof = try prover.prove(&program, 0x1000, null, 1000);
    defer proof.deinit();

    std.debug.print("✓ Proof generated successfully\n", .{});
    std.debug.print("  - Execution steps: {d}\n", .{proof.public_io.num_steps});
    std.debug.print("  - Lookup proofs: {d}\n", .{proof.lookup_proofs.items.len});
    std.debug.print("  - Constraint variables: {d}\n", .{proof.metadata.num_vars});
}

/// Demo 3: Proof serialization and deserialization
fn serializationDemo(allocator: std.mem.Allocator) !void {
    std.debug.print("Testing proof serialization...\n", .{});

    // Generate a proof
    const program = [_]u8{
        0x93, 0x00, 0xA0, 0x02, // ADDI x1, x0, 42
        0x00, 0x00, 0x00, 0x00, // Halt
    };

    var prover = try Prover(BabyBear).init(allocator, 99999);
    defer prover.deinit();

    var proof = try prover.prove(&program, 0x1000, null, 100);
    defer proof.deinit();

    // Serialize to bytes
    const serializer = BinarySerializer(BabyBear);
    const serialized = try serializer.serialize(allocator, proof);
    defer allocator.free(serialized);

    std.debug.print("✓ Serialized to {d} bytes\n", .{serialized.len});

    // Deserialize
    var deserialized = try serializer.deserialize(allocator, serialized);
    defer deserialized.deinit();

    std.debug.print("✓ Deserialized successfully\n", .{});
    std.debug.print("  - Program hash matches: {}\n", .{
        std.mem.eql(u8, &proof.public_io.program_hash, &deserialized.public_io.program_hash),
    });
    std.debug.print("  - Final PC matches: {}\n", .{
        proof.public_io.final_pc == deserialized.public_io.final_pc,
    });
    std.debug.print("  - Num steps matches: {}\n", .{
        proof.public_io.num_steps == deserialized.public_io.num_steps,
    });

    // Save to file
    const file = try std.fs.cwd().createFile("proof.bin", .{});
    defer file.close();
    try file.writeAll(serialized);

    std.debug.print("✓ Saved proof to proof.bin\n", .{});

    // Load from file
    const loaded = try std.fs.cwd().readFileAlloc(allocator, "proof.bin", 10 * 1024 * 1024);
    defer allocator.free(loaded);

    var loaded_proof = try serializer.deserialize(allocator, loaded);
    defer loaded_proof.deinit();

    std.debug.print("✓ Loaded proof from proof.bin\n", .{});
    std.debug.print("  - Verification would happen here in a full system\n", .{});
}
