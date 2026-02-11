const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // -- hash-zig dependency (fields + poseidon2) --
    // After running: zig fetch --save git+https://github.com/blockblaz/hash-zig
    // uncomment the lines below and adjust the module name if needed.
    //
    const hash_zig_dep = b.dependency("hash_zig", .{
         .target = target,
         .optimize = optimize,
    });
    const hash_zig_mod = hash_zig_dep.module("hash-zig");

    // -- main executable (for experimentation / demos) --
    const exe = b.addExecutable(.{
        .name = "zigz",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    exe.root_module.addImport("hash-zig", hash_zig_mod);
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }
    const run_step = b.step("run", "Run zigz");
    run_step.dependOn(&run_cmd.step);

    // -- zigz library module (for examples; uses path-based imports under src/) --
    const zigz_lib = b.addStaticLibrary(.{
        .name = "zigz",
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    zigz_lib.root_module.addImport("hash-zig", hash_zig_mod);

    // -- example executables --
    const example_sources = .{
        .{ "sumcheck_basic", "examples/sumcheck_basic.zig" },
        .{ "sumcheck_dishonest", "examples/sumcheck_dishonest.zig" },
        .{ "sumcheck_scalability", "examples/sumcheck_scalability.zig" },
    };
    inline for (example_sources) |entry| {
        const exe_name = entry.@"0";
        const exe_path = entry.@"1";
        const example_exe = b.addExecutable(.{
            .name = exe_name,
            .root_source_file = b.path(exe_path),
            .target = target,
            .optimize = optimize,
        });
        example_exe.root_module.addImport("zigz", zigz_lib.root_module);
        b.installArtifact(example_exe);
    }

    // -- tests --
    const unit_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    unit_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_unit_tests = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);

    // -- modular tests (for testing individual components) --
    // Phase 1: Field arithmetic tests
    const field_tests = b.addTest(.{
        .root_source_file = b.path("src/core/field.zig"),
        .target = target,
        .optimize = optimize,
    });
    field_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_field_tests = b.addRunArtifact(field_tests);
    const field_test_step = b.step("test-field", "Run field arithmetic tests");
    field_test_step.dependOn(&run_field_tests.step);

    // Phase 2: Polynomial tests
    const poly_tests = b.addTest(.{
        .root_source_file = b.path("src/poly/multilinear.zig"),
        .target = target,
        .optimize = optimize,
    });
    poly_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_poly_tests = b.addRunArtifact(poly_tests);
    const poly_test_step = b.step("test-poly", "Run polynomial tests");
    poly_test_step.dependOn(&run_poly_tests.step);

    // Phase 3: Sumcheck protocol tests
    const sumcheck_tests = b.addTest(.{
        .root_source_file = b.path("src/proofs/sumcheck_prover.zig"),
        .target = target,
        .optimize = optimize,
    });
    sumcheck_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_sumcheck_tests = b.addRunArtifact(sumcheck_tests);
    const sumcheck_test_step = b.step("test-sumcheck", "Run sumcheck protocol tests");
    sumcheck_test_step.dependOn(&run_sumcheck_tests.step);

    // Phase 4: ISA tests
    const isa_tests = b.addTest(.{
        .root_source_file = b.path("src/isa/rv32i.zig"),
        .target = target,
        .optimize = optimize,
    });
    isa_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_isa_tests = b.addRunArtifact(isa_tests);
    const isa_test_step = b.step("test-isa", "Run RISC-V ISA tests");
    isa_test_step.dependOn(&run_isa_tests.step);

    // Phase 5: Lasso lookup argument tests
    const lasso_tests = b.addTest(.{
        .root_source_file = b.path("src/lookups/lasso_prover.zig"),
        .target = target,
        .optimize = optimize,
    });
    lasso_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_lasso_tests = b.addRunArtifact(lasso_tests);
    const lasso_test_step = b.step("test-lasso", "Run Lasso lookup argument tests");
    lasso_test_step.dependOn(&run_lasso_tests.step);

    // Phase 6: Polynomial commitment tests
    const commit_tests = b.addTest(.{
        .root_source_file = b.path("src/commitments/polynomial_commit.zig"),
        .target = target,
        .optimize = optimize,
    });
    commit_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_commit_tests = b.addRunArtifact(commit_tests);
    const commit_test_step = b.step("test-commit", "Run polynomial commitment tests");
    commit_test_step.dependOn(&run_commit_tests.step);

    // Add more modular test steps as modules are implemented
}
