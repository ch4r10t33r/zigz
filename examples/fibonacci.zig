const std = @import("std");
const zigz = @import("zigz");

/// Fibonacci host — proves execution of a compiled Zig guest program.
///
/// Architecture (mirrors SP1's fibonacci example):
///
///   SP1                              zigz
///   ─────────────────────────────    ─────────────────────────────────────
///   Write Rust guest                 Write Zig guest (fibonacci_guest/)
///   Compile → RISC-V ELF via sp1up  Compile → RISC-V ELF via zig build
///   sp1_sdk::prove(ELF, input)       zigz::Prover::prove(elf_bytes, ...)
///   sp1_sdk::verify(proof, ELF)      zigz::Verifier::verify(proof, elf_bytes)
///
/// The guest ELF (fibonacci_guest) is installed alongside this binary by
/// `zig build fibonacci`.  The host locates it at runtime via its own path.
///
/// Run:
///   zig build fibonacci
///   ./zig-out/bin/fibonacci
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Locate the guest ELF: it is installed next to this executable.
    const exe_dir = try std.fs.selfExeDirPathAlloc(allocator);
    defer allocator.free(exe_dir);
    const guest_path = try std.fs.path.join(allocator, &.{ exe_dir, "fibonacci_guest" });
    defer allocator.free(guest_path);

    const guest_elf = std.fs.cwd().readFileAlloc(allocator, guest_path, 4 * 1024 * 1024) catch |err| {
        std.debug.print("error: cannot read guest ELF at {s}: {}\n", .{ guest_path, err });
        std.debug.print("hint: run `zig build fibonacci` first\n", .{});
        return err;
    };
    defer allocator.free(guest_elf);

    const F = zigz.BabyBear;
    const n: u64 = 10;
    const expected_fib_n: u64 = 55; // fib(10)
    const expected_fib_n1: u64 = 89; // fib(11)

    // Input tape: the guest reads n via io.read(u64).
    const input = [_]u64{n};

    std.debug.print("\n=== zigz: Fibonacci zkVM Demo (n={d}) ===\n\n", .{n});
    std.debug.print("Guest ELF : {s} ({d} bytes)\n", .{ guest_path, guest_elf.len });
    std.debug.print("Input     : n = {d} (via io.read)\n", .{n});
    std.debug.print("Expected  : outputs[0] = fib({d}) = {d},  outputs[1] = fib({d}) = {d}\n\n", .{
        n, expected_fib_n, n + 1, expected_fib_n1,
    });

    // -------------------------------------------------------------------------
    // Load the ELF: extract entry PC and PT_LOAD segments.
    // -------------------------------------------------------------------------
    const load_result = try zigz.elf.load(allocator, guest_elf);
    defer allocator.free(load_result.segments_owned);

    std.debug.print("ELF entry : 0x{x}\n", .{load_result.entry_pc});
    std.debug.print("Segments  : {d}\n\n", .{load_result.segments.len});

    // -------------------------------------------------------------------------
    // Prove: run the guest inside the zkVM and generate a succinct proof.
    // The proof cryptographically commits to every execution step via
    // Sumcheck + Lasso + Merkle.  The prover's work scales linearly with
    // the number of steps; the verifier's work is O(log steps).
    // -------------------------------------------------------------------------
    std.debug.print("Proving execution...\n", .{});

    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    const t0 = std.time.milliTimestamp();
    var proof = try prover.prove(
        guest_elf,
        load_result.entry_pc,
        null,
        1 << 20,
        load_result.segments,
        &input,
    );
    defer proof.deinit();
    const prove_ms = std.time.milliTimestamp() - t0;

    std.debug.print("  Steps    : {d}\n", .{proof.metadata.num_steps});
    std.debug.print("  log₂     : {d}  (verifier complexity)\n", .{proof.metadata.num_vars});
    std.debug.print("  Size     : ~{d} bytes\n", .{proof.estimateSize()});
    std.debug.print("  Time     : {d} ms\n\n", .{prove_ms});

    // -------------------------------------------------------------------------
    // Check public outputs: the guest called io.commit(a) and io.commit(b)
    // which appended to proof.public_io.outputs in call order.
    // -------------------------------------------------------------------------
    const outputs = proof.public_io.outputs orelse {
        std.debug.print("ERROR: guest committed no outputs\n", .{});
        return error.NoOutputs;
    };

    std.debug.print("Outputs (via io.commit):\n", .{});
    std.debug.print("  outputs[0] = fib({d}) = {d}  (expected {d})\n", .{ n, outputs[0], expected_fib_n });
    std.debug.print("  outputs[1] = fib({d}) = {d}  (expected {d})\n\n", .{ n + 1, outputs[1], expected_fib_n1 });

    if (outputs[0] != expected_fib_n or outputs[1] != expected_fib_n1) {
        std.debug.print("ERROR: unexpected output — computation is wrong!\n", .{});
        return error.WrongOutput;
    }

    // -------------------------------------------------------------------------
    // Verify: check the proof without re-executing.
    // The verifier only needs the proof + original ELF bytes; it does O(log n)
    // work regardless of how many instructions the guest executed.
    // -------------------------------------------------------------------------
    std.debug.print("Verifying proof...\n", .{});

    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const t1 = std.time.milliTimestamp();
    const result = try verifier.verify(proof, guest_elf);
    const verify_ms = std.time.milliTimestamp() - t1;

    std.debug.print("  Result   : {s}\n", .{@tagName(result)});
    std.debug.print("  Time     : {d} ms", .{verify_ms});
    if (verify_ms > 0) {
        std.debug.print("  ({d:.1}× faster than proving)\n", .{
            @as(f64, @floatFromInt(prove_ms)) / @as(f64, @floatFromInt(verify_ms)),
        });
    } else {
        std.debug.print("\n", .{});
    }

    std.debug.print("\n", .{});
    if (result == .Accept) {
        std.debug.print(
            \\✓  Proved: fib({d}) = {d}
            \\   Verifier did O(log {d}) = O({d}) work — no re-execution.
            \\
        , .{ n, expected_fib_n, proof.metadata.num_steps, proof.metadata.num_vars });
    } else {
        std.debug.print("✗  Proof rejected: {s}\n", .{@tagName(result)});
        return error.VerificationFailed;
    }
}
