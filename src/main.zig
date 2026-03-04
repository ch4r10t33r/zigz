const std = @import("std");
const zigz = @import("zigz");

const F = zigz.BabyBear;
const default_entry_pc: u64 = 0x1000;
const default_max_steps: usize = 1 << 20;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len < 2) {
        printUsage();
        return;
    }

    if (std.mem.eql(u8, args[1], "execute")) {
        return cmdExecute(allocator, args[2..]);
    }
    if (std.mem.eql(u8, args[1], "prove")) {
        return cmdProve(allocator, args[2..]);
    }
    if (std.mem.eql(u8, args[1], "verify")) {
        return cmdVerify(allocator, args[2..]);
    }
    if (std.mem.eql(u8, args[1], "new")) {
        return cmdNew(allocator, args[2..]);
    }
    if (std.mem.eql(u8, args[1], "build")) {
        return cmdBuild(allocator, args[2..]);
    }

    // No subcommand: print banner (backward compatible)
    const stdout = std.io.getStdOut().writer();
    try stdout.print("zigz — Jolt-style zkVM (sumcheck + Lasso)\n", .{});
    try stdout.print("Usage: zigz <execute|prove|verify|new|build> [args...]\n", .{});
}

fn printUsage() void {
    const stdout = std.io.getStdOut().writer();
    stdout.print(
        \\zigz — Jolt-style zkVM (sumcheck + Lasso)
        \\
        \\  zigz execute <program.bin|program.elf> [--entry 0x1000] [--max-steps N]
        \\    Run VM only (no proof). ELF: entry from file; raw .bin: use --entry.
        \\
        \\  zigz prove <program.bin|program.elf> [--entry 0x1000] [--max-steps N] [--out proof.bin]
        \\    Generate proof. ELF: entry and segments from file.
        \\
        \\  zigz verify <proof.bin> <program.bin|program.elf>
        \\    Verify proof. Program must match the one used to prove.
        \\
        \\  zigz new <name>
        \\    Create a new RISC-V project template in directory <name>.
        \\
        \\  zigz build [path]
        \\    Build project (RISC-V ELF). Default path: current directory.
        \\    Output: <path>/zig-out/bin/program (ELF for zigz execute/prove).
        \\
    , .{}) catch {};
}

fn parseOptionalU64(args: []const []const u8, flag: []const u8) ?u64 {
    for (args, 0..) |arg, i| {
        if (!std.mem.eql(u8, arg, flag)) continue;
        if (i + 1 >= args.len) return null;
        const next = args[i + 1];
        if (std.mem.startsWith(u8, next, "0x")) {
            return std.fmt.parseInt(u64, next[2..], 16) catch null;
        }
        return std.fmt.parseInt(u64, next, 10) catch null;
    }
    return null;
}

fn parseOptionalOut(args: []const []const u8) ?[]const u8 {
    for (args, 0..) |arg, i| {
        if (!std.mem.eql(u8, arg, "--out")) continue;
        if (i + 1 >= args.len) return null;
        return args[i + 1];
    }
    return null;
}

fn cmdExecute(allocator: std.mem.Allocator, args: []const []const u8) !void {
    if (args.len == 0) {
        std.debug.print("error: execute requires <program.bin|program.elf>\n", .{});
        printUsage();
        return error.InvalidArgs;
    }
    const program_path = args[0];
    const default_entry = parseOptionalU64(args, "--entry") orelse default_entry_pc;
    const max_steps = parseOptionalU64(args, "--max-steps") orelse default_max_steps;

    const program = try std.fs.cwd().readFileAlloc(allocator, program_path, 16 * 1024 * 1024);
    defer allocator.free(program);

    var vm: zigz.VMState = if (zigz.elf.isElf(program)) blk: {
        const load_result = try zigz.elf.load(allocator, program);
        defer allocator.free(load_result.segments_owned);
        break :blk try zigz.VMState.initFromSegments(allocator, load_result.segments, load_result.entry_pc);
    } else blk: {
        break :blk try zigz.VMState.init(allocator, program, default_entry);
    };
    defer vm.deinit();

    const entry_pc = vm.pc;
    var steps: usize = 0;
    while (!vm.halted and steps < max_steps) : (steps += 1) {
        vm.step() catch |err| {
            if (err == error.InvalidInstruction) break;
            return err;
        };
    }

    const stdout = std.io.getStdOut().writer();
    try stdout.print("execute: {d} steps (entry_pc=0x{x}, max_steps={d})\n", .{ steps, entry_pc, max_steps });
}

fn cmdProve(allocator: std.mem.Allocator, args: []const []const u8) !void {
    if (args.len == 0) {
        std.debug.print("error: prove requires <program.bin|program.elf>\n", .{});
        printUsage();
        return error.InvalidArgs;
    }
    const program_path = args[0];
    const default_entry = parseOptionalU64(args, "--entry") orelse default_entry_pc;
    const max_steps_val = parseOptionalU64(args, "--max-steps");
    const max_steps: usize = if (max_steps_val) |v| @intCast(v) else default_max_steps;
    const out_path = parseOptionalOut(args);

    const program = try std.fs.cwd().readFileAlloc(allocator, program_path, 16 * 1024 * 1024);
    defer allocator.free(program);

    var load_result: ?zigz.elf.LoadResult = null;
    if (zigz.elf.isElf(program)) {
        load_result = try zigz.elf.load(allocator, program);
    }
    defer if (load_result) |*lr| allocator.free(lr.segments_owned);

    const entry_pc = if (load_result) |*lr| lr.entry_pc else default_entry;
    const segments: ?[]const zigz.elf.Segment = if (load_result) |*lr| lr.segments else null;

    var prover = try zigz.Prover(F).init(allocator, 0);
    defer prover.deinit();

    const start = std.time.milliTimestamp();
    var proof = try prover.prove(program, entry_pc, null, max_steps, segments);
    defer proof.deinit();
    const prove_ms = std.time.milliTimestamp() - start;

    const serializer = zigz.serialization.BinarySerializer(F);
    const proof_bytes = try serializer.serialize(allocator, proof);
    defer allocator.free(proof_bytes);

    if (out_path) |path| {
        try std.fs.cwd().writeFile(.{ .sub_path = path, .data = proof_bytes });
    }

    const stdout = std.io.getStdOut().writer();
    try stdout.print("prove: {d} ms, proof size {d} bytes, steps {d}\n", .{
        prove_ms,
        proof_bytes.len,
        proof.metadata.num_steps,
    });
    if (out_path) |path| try stdout.print("wrote proof to {s}\n", .{path});
}

fn cmdVerify(allocator: std.mem.Allocator, args: []const []const u8) !void {
    if (args.len < 2) {
        std.debug.print("error: verify requires <proof.bin> <program.bin>\n", .{});
        printUsage();
        return error.InvalidArgs;
    }
    const proof_path = args[0];
    const program_path = args[1];

    const proof_bytes = try std.fs.cwd().readFileAlloc(allocator, proof_path, 32 * 1024 * 1024);
    defer allocator.free(proof_bytes);

    const program = try std.fs.cwd().readFileAlloc(allocator, program_path, 16 * 1024 * 1024);
    defer allocator.free(program);

    const serializer = zigz.serialization.BinarySerializer(F);
    var proof = try serializer.deserialize(allocator, proof_bytes);
    defer proof.deinit();

    var verifier = zigz.Verifier(F).init(allocator);
    defer verifier.deinit();

    const start = std.time.milliTimestamp();
    const result = try verifier.verify(proof, program);
    const verify_ms = std.time.milliTimestamp() - start;

    const stdout = std.io.getStdOut().writer();
    try stdout.print("verify: {s} ({d} ms)\n", .{ @tagName(result), verify_ms });
}

fn cmdNew(_: std.mem.Allocator, args: []const []const u8) !void {
    if (args.len == 0) {
        std.debug.print("error: new requires <name>\n", .{});
        printUsage();
        return error.InvalidArgs;
    }
    const name = args[0];
    if (name.len == 0 or name[0] == '-') {
        std.debug.print("error: invalid project name\n", .{});
        return error.InvalidArgs;
    }
    var dir = try std.fs.cwd().makeOpenPath(name, .{});
    defer dir.close();
    try dir.makePath("src");
    const build_zig =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const target = b.resolveTargetQuery(.{
        \\        .cpu_arch = .riscv64,
        \\        .os_tag = .linux,
        \\    });
        \\    const optimize = b.standardOptimizeOption(.{});
        \\    const exe = b.addExecutable(.{
        \\        .name = "program",
        \\        .root_source_file = b.path("src/main.zig"),
        \\        .target = target,
        \\        .optimize = optimize,
        \\    });
        \\    b.installArtifact(exe);
        \\}
    ;
    try dir.writeFile(.{ .sub_path = "build.zig", .data = build_zig });
    const main_zig =
        \\// Minimal RISC-V program for zigz zkVM.
        \\// Build: zig build
        \\// Run: zigz execute zig-out/bin/program
        \\// Prove: zigz prove zig-out/bin/program
        \\pub fn main() u8 {
        \\    return 0;
        \\}
    ;
    try dir.writeFile(.{ .sub_path = "src/main.zig", .data = main_zig });
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Created project \"{s}\".\n", .{name});
    try stdout.print("  cd {s} && zig build && zigz execute zig-out/bin/program\n", .{name});
}

fn cmdBuild(allocator: std.mem.Allocator, args: []const []const u8) !void {
    const path = if (args.len > 0) args[0] else ".";
    var dir = std.fs.cwd().openDir(path, .{}) catch |err| {
        std.debug.print("error: cannot open directory \"{s}\": {}\n", .{ path, err });
        return err;
    };
    defer dir.close();
    dir.access("build.zig", .{}) catch |err| {
        std.debug.print("error: no build.zig in \"{s}\" ({})\n", .{ path, err });
        return error.InvalidArgs;
    };
    const zig_exe = try findZigExe(allocator);
    defer allocator.free(zig_exe);
    var argv_buf: [2][]const u8 = .{ zig_exe, "build" };
    const argv = argv_buf[0..];
    const result = std.process.Child.run(.{
        .allocator = allocator,
        .argv = argv,
        .cwd = path,
    }) catch |err| {
        std.debug.print("error: failed to run zig build: {}\n", .{err});
        return err;
    };
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);
    if (result.term.Exited != 0) {
        if (result.stderr.len > 0) std.debug.print("{s}", .{result.stderr});
        std.process.exit(result.term.Exited);
    }
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Build succeeded. ELF: {s}/zig-out/bin/program\n", .{path});
}

fn findZigExe(allocator: std.mem.Allocator) ![]const u8 {
    const self_exe = try std.fs.selfExePathAlloc(allocator);
    defer allocator.free(self_exe);
    const dir = std.fs.path.dirname(self_exe) orelse ".";
    const sep = std.fs.path.sep_str;
    const zig_in_same_dir = try std.fmt.allocPrint(allocator, "{s}{s}zig", .{ dir, sep });
    defer allocator.free(zig_in_same_dir);
    const f = std.fs.openFileAbsolute(zig_in_same_dir, .{}) catch {
        return allocator.dupe(u8, "zig");
    };
    f.close();
    return std.fs.realpathAlloc(allocator, zig_in_same_dir);
}

test "basic sanity" {
    try std.testing.expect(true);
}
