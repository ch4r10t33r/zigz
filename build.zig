const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // -- hash-zig dependency (fields + poseidon2) --
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
        .{ "babybear_demo", "examples/babybear_demo.zig" },
        .{ "prover_demo", "examples/prover_demo.zig" },
        .{ "prover_verifier_demo", "examples/prover_verifier_demo.zig" },
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

    // Phase 4b: RV64I tests
    const rv64i_tests = b.addTest(.{
        .root_source_file = b.path("src/isa/rv64i.zig"),
        .target = target,
        .optimize = optimize,
    });
    rv64i_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_rv64i_tests = b.addRunArtifact(rv64i_tests);
    const rv64i_test_step = b.step("test-rv64i", "Run RISC-V RV64I tests");
    rv64i_test_step.dependOn(&run_rv64i_tests.step);

    // RV64I integration tests (VM execution)
    const rv64i_vm_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_rv64i.zig"),
        .target = target,
        .optimize = optimize,
    });
    rv64i_vm_tests.root_module.addImport("zigz", zigz_lib.root_module);
    rv64i_vm_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_rv64i_vm_tests = b.addRunArtifact(rv64i_vm_tests);
    const rv64i_vm_test_step = b.step("test-rv64i-vm", "Run RV64I VM execution tests");
    rv64i_vm_test_step.dependOn(&run_rv64i_vm_tests.step);

    // Phase 5: Lasso lookup argument tests (via zigz lib so imports resolve)
    const lasso_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_lasso.zig"),
        .target = target,
        .optimize = optimize,
        .filters = &[1][]const u8{"lasso_prover"},
    });
    lasso_tests.root_module.addImport("zigz", zigz_lib.root_module);
    lasso_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_lasso_tests = b.addRunArtifact(lasso_tests);
    const lasso_test_step = b.step("test-lasso", "Run Lasso lookup argument tests");
    lasso_test_step.dependOn(&run_lasso_tests.step);

    // Phase 6: Polynomial commitment tests (via zigz lib so imports resolve)
    const commit_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_commit.zig"),
        .target = target,
        .optimize = optimize,
        .filters = &[1][]const u8{"polynomial_commit"},
    });
    commit_tests.root_module.addImport("zigz", zigz_lib.root_module);
    commit_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_commit_tests = b.addRunArtifact(commit_tests);
    const commit_test_step = b.step("test-commit", "Run polynomial commitment tests");
    commit_test_step.dependOn(&run_commit_tests.step);

    // Phase 7: VM state machine tests (via zigz lib so imports resolve)
    const vm_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_vm.zig"),
        .target = target,
        .optimize = optimize,
        .filters = &[1][]const u8{"vm:"},
    });
    vm_tests.root_module.addImport("zigz", zigz_lib.root_module);
    vm_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_vm_tests = b.addRunArtifact(vm_tests);
    const vm_test_step = b.step("test-vm", "Run VM state machine tests");
    vm_test_step.dependOn(&run_vm_tests.step);

    // Phase 8: Constraint generation tests (via zigz lib so imports resolve)
    const constraint_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_constraints.zig"),
        .target = target,
        .optimize = optimize,
        .filters = &[1][]const u8{"constraints:"},
    });
    constraint_tests.root_module.addImport("zigz", zigz_lib.root_module);
    constraint_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_constraint_tests = b.addRunArtifact(constraint_tests);
    const constraint_test_step = b.step("test-constraints", "Run constraint generation tests");
    constraint_test_step.dependOn(&run_constraint_tests.step);

    // Phase 9: Full prover tests (via zigz lib so imports resolve)
    const prover_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_prover.zig"),
        .target = target,
        .optimize = optimize,
        .filters = &[1][]const u8{"prover:"},
    });
    prover_tests.root_module.addImport("zigz", zigz_lib.root_module);
    prover_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_prover_tests = b.addRunArtifact(prover_tests);
    const prover_test_step = b.step("test-prover", "Run full prover tests");
    prover_test_step.dependOn(&run_prover_tests.step);

    // Phase 10: Full verifier tests (via zigz lib so imports resolve)
    const verifier_tests = b.addTest(.{
        .root_source_file = b.path("tests/test_verifier.zig"),
        .target = target,
        .optimize = optimize,
        .filters = &[1][]const u8{"verifier:"},
    });
    verifier_tests.root_module.addImport("zigz", zigz_lib.root_module);
    verifier_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_verifier_tests = b.addRunArtifact(verifier_tests);
    const verifier_test_step = b.step("test-verifier", "Run full verifier tests");
    verifier_test_step.dependOn(&run_verifier_tests.step);

    // Verifier benchmarks: run benchmarks.main() via zigz lib so path imports resolve
    const verifier_bench = b.addExecutable(.{
        .name = "verifier_bench",
        .root_source_file = b.path("src/bench_runner.zig"),
        .target = target,
        .optimize = optimize,
    });
    verifier_bench.root_module.addImport("zigz", zigz_lib.root_module);
    b.installArtifact(verifier_bench);

    const run_verifier_bench = b.addRunArtifact(verifier_bench);
    run_verifier_bench.step.dependOn(b.getInstallStep());
    const bench_step = b.step("bench", "Run verifier benchmarks");
    bench_step.dependOn(&run_verifier_bench.step);

    // Integration tests (end-to-end prover-verifier)
    const integration_tests = b.addTest(.{
        .root_source_file = b.path("tests/integration_tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    integration_tests.root_module.addImport("zigz", zigz_lib.root_module);
    integration_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_integration_tests = b.addRunArtifact(integration_tests);
    const integration_test_step = b.step("test-integration", "Run integration tests");
    integration_test_step.dependOn(&run_integration_tests.step);

    // Comprehensive test step (runs all tests)
    const all_tests_step = b.step("test-all", "Run all tests");
    all_tests_step.dependOn(test_step);
    all_tests_step.dependOn(field_test_step);
    all_tests_step.dependOn(poly_test_step);
    all_tests_step.dependOn(sumcheck_test_step);
    all_tests_step.dependOn(isa_test_step);
    all_tests_step.dependOn(rv64i_test_step);
    all_tests_step.dependOn(rv64i_vm_test_step);
    all_tests_step.dependOn(lasso_test_step);
    all_tests_step.dependOn(commit_test_step);
    all_tests_step.dependOn(vm_test_step);
    all_tests_step.dependOn(constraint_test_step);
    all_tests_step.dependOn(prover_test_step);
    all_tests_step.dependOn(verifier_test_step);
    all_tests_step.dependOn(integration_test_step);
}
