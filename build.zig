const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // -- hash-zig dependency (fields + poseidon2) --
    const hash_zig_dep = b.dependency("hash_zig", .{});
    const hash_zig_mod = hash_zig_dep.module("hash-zig");

    // -- main executable (for experimentation / demos) --
    const exe = b.addExecutable(.{
        .name = "zigz",
    });
    exe.setTarget(target);
    exe.setBuildMode(optimize);
    exe.root_module.addRootSourceFile(b.path("src/main.zig"));
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
    });
    zigz_lib.setTarget(target);
    zigz_lib.setBuildMode(optimize);
    zigz_lib.root_module.addRootSourceFile(b.path("src/lib.zig"));
    zigz_lib.root_module.addImport("hash-zig", hash_zig_mod);

    // -- example executables --
    const example_sources = .{
        .{ "sumcheck_basic", "examples/sumcheck_basic.zig" },
        .{ "sumcheck_dishonest", "examples/sumcheck_dishonest.zig" },
        .{ "sumcheck_scalability", "examples/sumcheck_scalability.zig" },
        .{ "babybear_demo", "examples/babybear_demo.zig" },
        .{ "prover_demo", "examples/prover_demo.zig" },
    };
    inline for (example_sources) |entry| {
        const exe_name = entry.@"0";
        const exe_path = entry.@"1";
        const example_exe = b.addExecutable(.{
            .name = exe_name,
        });
        example_exe.setTarget(target);
        example_exe.setBuildMode(optimize);
        example_exe.root_module.addRootSourceFile(b.path(exe_path));
        example_exe.root_module.addImport("zigz", zigz_lib.root_module);
        b.installArtifact(example_exe);
    }

    // -- tests --
    const unit_tests = b.addTest(.{});
    unit_tests.setTarget(target);
    unit_tests.setBuildMode(optimize);
    unit_tests.root_module.addRootSourceFile(b.path("src/main.zig"));
    unit_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_unit_tests = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);

    // -- modular tests (for testing individual components) --
    // Phase 1: Field arithmetic tests
    const field_tests = b.addTest(.{});
    field_tests.setTarget(target);
    field_tests.setBuildMode(optimize);
    field_tests.root_module.addRootSourceFile(b.path("src/core/field.zig"));
    field_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_field_tests = b.addRunArtifact(field_tests);
    const field_test_step = b.step("test-field", "Run field arithmetic tests");
    field_test_step.dependOn(&run_field_tests.step);

    // Phase 2: Polynomial tests
    const poly_tests = b.addTest(.{});
    poly_tests.setTarget(target);
    poly_tests.setBuildMode(optimize);
    poly_tests.root_module.addRootSourceFile(b.path("src/poly/multilinear.zig"));
    poly_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_poly_tests = b.addRunArtifact(poly_tests);
    const poly_test_step = b.step("test-poly", "Run polynomial tests");
    poly_test_step.dependOn(&run_poly_tests.step);

    // Phase 3: Sumcheck protocol tests
    const sumcheck_tests = b.addTest(.{});
    sumcheck_tests.setTarget(target);
    sumcheck_tests.setBuildMode(optimize);
    sumcheck_tests.root_module.addRootSourceFile(b.path("src/proofs/sumcheck_prover.zig"));
    sumcheck_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_sumcheck_tests = b.addRunArtifact(sumcheck_tests);
    const sumcheck_test_step = b.step("test-sumcheck", "Run sumcheck protocol tests");
    sumcheck_test_step.dependOn(&run_sumcheck_tests.step);

    // Phase 4: ISA tests
    const isa_tests = b.addTest(.{});
    isa_tests.setTarget(target);
    isa_tests.setBuildMode(optimize);
    isa_tests.root_module.addRootSourceFile(b.path("src/isa/rv32i.zig"));
    isa_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_isa_tests = b.addRunArtifact(isa_tests);
    const isa_test_step = b.step("test-isa", "Run RISC-V ISA tests");
    isa_test_step.dependOn(&run_isa_tests.step);

    // Phase 5: Lasso lookup argument tests
    const lasso_tests = b.addTest(.{});
    lasso_tests.setTarget(target);
    lasso_tests.setBuildMode(optimize);
    lasso_tests.root_module.addRootSourceFile(b.path("src/lookups/lasso_prover.zig"));
    lasso_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_lasso_tests = b.addRunArtifact(lasso_tests);
    const lasso_test_step = b.step("test-lasso", "Run Lasso lookup argument tests");
    lasso_test_step.dependOn(&run_lasso_tests.step);

    // Phase 6: Polynomial commitment tests
    const commit_tests = b.addTest(.{});
    commit_tests.setTarget(target);
    commit_tests.setBuildMode(optimize);
    commit_tests.root_module.addRootSourceFile(b.path("src/commitments/polynomial_commit.zig"));
    commit_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_commit_tests = b.addRunArtifact(commit_tests);
    const commit_test_step = b.step("test-commit", "Run polynomial commitment tests");
    commit_test_step.dependOn(&run_commit_tests.step);

    // Phase 7: VM state machine tests
    const vm_tests = b.addTest(.{});
    vm_tests.setTarget(target);
    vm_tests.setBuildMode(optimize);
    vm_tests.root_module.addRootSourceFile(b.path("src/vm/state.zig"));
    vm_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_vm_tests = b.addRunArtifact(vm_tests);
    const vm_test_step = b.step("test-vm", "Run VM state machine tests");
    vm_test_step.dependOn(&run_vm_tests.step);

    // Phase 8: Constraint generation tests
    const constraint_tests = b.addTest(.{});
    constraint_tests.setTarget(target);
    constraint_tests.setBuildMode(optimize);
    constraint_tests.root_module.addRootSourceFile(b.path("src/constraints/builder.zig"));
    constraint_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_constraint_tests = b.addRunArtifact(constraint_tests);
    const constraint_test_step = b.step("test-constraints", "Run constraint generation tests");
    constraint_test_step.dependOn(&run_constraint_tests.step);

    // Phase 9: Full prover tests
    const prover_tests = b.addTest(.{});
    prover_tests.setTarget(target);
    prover_tests.setBuildMode(optimize);
    prover_tests.root_module.addRootSourceFile(b.path("src/prover/prover.zig"));
    prover_tests.root_module.addImport("hash-zig", hash_zig_mod);
    const run_prover_tests = b.addRunArtifact(prover_tests);
    const prover_test_step = b.step("test-prover", "Run full prover tests");
    prover_test_step.dependOn(&run_prover_tests.step);

    // Add more modular test steps as modules are implemented
}
