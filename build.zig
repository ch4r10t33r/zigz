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

    // -- zigz module (used as an import by the exe, examples, and tests) --
    const zigz_mod = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    zigz_mod.addImport("hash-zig", hash_zig_mod);

    // -- main executable (CLI: execute | prove | verify) --
    const exe = b.addExecutable(.{
        .name = "zigz",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
                .{ .name = "zigz", .module = zigz_mod },
            },
        }),
    });
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }
    const run_step = b.step("run", "Run zigz");
    run_step.dependOn(&run_cmd.step);

    // -- example executables (use zigz module) --
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
            .root_module = b.createModule(.{
                .root_source_file = b.path(exe_path),
                .target = target,
                .optimize = optimize,
                .imports = &.{
                    .{ .name = "zigz", .module = zigz_mod },
                },
            }),
        });
        b.installArtifact(example_exe);
    }

    // -- fibonacci example: cross-compiles a Zig guest to RISC-V, then proves it --
    //
    // This is the zigz equivalent of SP1's fibonacci example:
    //   SP1: write Rust guest → compile → sp1_sdk::prove(ELF)
    //   zigz: write Zig guest → compile → zigz::Prover::prove(elf_bytes)
    //
    // The guest (examples/fibonacci_guest/src/main.zig) targets riscv64-freestanding.
    // Both guest and host are installed to zig-out/bin/; the host locates the
    // guest at runtime via std.fs.selfExeDirPathAlloc().
    // Restrict the guest to rv64im only — zigz's VM supports RV64I+M.
    // Disable C (compressed), A (atomics), F/D (float), Zicsr, Zifencei.
    const riscv_target = b.resolveTargetQuery(.{
        .cpu_arch = .riscv64,
        .os_tag = .freestanding,
        .abi = .none,
        .cpu_model = .{ .explicit = &std.Target.riscv.cpu.generic_rv64 },
        .cpu_features_add = std.Target.riscv.featureSet(&.{.m}),
        .cpu_features_sub = std.Target.riscv.featureSet(&.{ .a, .c, .d, .f, .zicsr, .zifencei }),
    });
    const fibonacci_guest = b.addExecutable(.{
        .name = "fibonacci_guest",
        .root_module = b.createModule(.{
            .root_source_file = b.path("examples/fibonacci_guest/src/main.zig"),
            .target = riscv_target,
            .optimize = .ReleaseSmall,
        }),
    });
    b.installArtifact(fibonacci_guest);

    const fibonacci_exe = b.addExecutable(.{
        .name = "fibonacci",
        .root_module = b.createModule(.{
            .root_source_file = b.path("examples/fibonacci.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
            },
        }),
    });
    b.installArtifact(fibonacci_exe);

    const fibonacci_run = b.addRunArtifact(fibonacci_exe);
    fibonacci_run.step.dependOn(b.getInstallStep());
    const fibonacci_step = b.step("fibonacci", "Run the Fibonacci zkVM example (guest + host)");
    fibonacci_step.dependOn(&fibonacci_run.step);

    // -- tests --
    const unit_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
                .{ .name = "zigz", .module = zigz_mod },
            },
        }),
    });
    const run_unit_tests = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);

    // -- modular tests (for testing individual components) --
    // Phase 1: Field arithmetic tests
    const field_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/core/field.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_field_tests = b.addRunArtifact(field_tests);
    const field_test_step = b.step("test-field", "Run field arithmetic tests");
    field_test_step.dependOn(&run_field_tests.step);

    // Phase 2: Polynomial tests
    const poly_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/poly/multilinear.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_poly_tests = b.addRunArtifact(poly_tests);
    const poly_test_step = b.step("test-poly", "Run polynomial tests");
    poly_test_step.dependOn(&run_poly_tests.step);

    // Phase 3: Sumcheck protocol tests
    // Uses lib.zig as root so that cross-directory imports within src/ resolve correctly.
    const sumcheck_tests = b.addTest(.{
        .filters = &[1][]const u8{"sumcheck"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_sumcheck_tests = b.addRunArtifact(sumcheck_tests);
    const sumcheck_test_step = b.step("test-sumcheck", "Run sumcheck protocol tests");
    sumcheck_test_step.dependOn(&run_sumcheck_tests.step);

    // Phase 4: ISA tests
    const isa_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/isa/rv32i.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_isa_tests = b.addRunArtifact(isa_tests);
    const isa_test_step = b.step("test-isa", "Run RISC-V ISA tests");
    isa_test_step.dependOn(&run_isa_tests.step);

    // Phase 4b: RV64I tests
    const rv64i_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/isa/rv64i.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_rv64i_tests = b.addRunArtifact(rv64i_tests);
    const rv64i_test_step = b.step("test-rv64i", "Run RISC-V RV64I tests");
    rv64i_test_step.dependOn(&run_rv64i_tests.step);

    // RV64I integration tests (VM execution)
    const rv64i_vm_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_rv64i.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_rv64i_vm_tests = b.addRunArtifact(rv64i_vm_tests);
    const rv64i_vm_test_step = b.step("test-rv64i-vm", "Run RV64I VM execution tests");
    rv64i_vm_test_step.dependOn(&run_rv64i_vm_tests.step);

    // RV64M extension tests (multiply/divide)
    const rv64m_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_rv64m.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_rv64m_tests = b.addRunArtifact(rv64m_tests);
    const rv64m_test_step = b.step("test-rv64m", "Run RV64M multiply/divide tests");
    rv64m_test_step.dependOn(&run_rv64m_tests.step);

    // Phase 5: Lasso lookup argument tests
    const lasso_tests = b.addTest(.{
        .filters = &[1][]const u8{"lasso_prover"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_lasso.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_lasso_tests = b.addRunArtifact(lasso_tests);
    const lasso_test_step = b.step("test-lasso", "Run Lasso lookup argument tests");
    lasso_test_step.dependOn(&run_lasso_tests.step);

    // Phase 6: Polynomial commitment tests
    const commit_tests = b.addTest(.{
        .filters = &[1][]const u8{"polynomial_commit"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_commit.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_commit_tests = b.addRunArtifact(commit_tests);
    const commit_test_step = b.step("test-commit", "Run polynomial commitment tests");
    commit_test_step.dependOn(&run_commit_tests.step);

    // Phase 7: VM state machine tests
    const vm_tests = b.addTest(.{
        .filters = &[1][]const u8{"vm:"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_vm.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_vm_tests = b.addRunArtifact(vm_tests);
    const vm_test_step = b.step("test-vm", "Run VM state machine tests");
    vm_test_step.dependOn(&run_vm_tests.step);

    // Phase 8: Constraint generation tests
    const constraint_tests = b.addTest(.{
        .filters = &[1][]const u8{"constraints:"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_constraints.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_constraint_tests = b.addRunArtifact(constraint_tests);
    const constraint_test_step = b.step("test-constraints", "Run constraint generation tests");
    constraint_test_step.dependOn(&run_constraint_tests.step);

    // Phase 9: Full prover tests
    const prover_tests = b.addTest(.{
        .filters = &[1][]const u8{"prover:"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_prover.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_prover_tests = b.addRunArtifact(prover_tests);
    const prover_test_step = b.step("test-prover", "Run full prover tests");
    prover_test_step.dependOn(&run_prover_tests.step);

    // Phase 10: Full verifier tests
    const verifier_tests = b.addTest(.{
        .filters = &[1][]const u8{"verifier:"},
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_verifier.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
    const run_verifier_tests = b.addRunArtifact(verifier_tests);
    const verifier_test_step = b.step("test-verifier", "Run full verifier tests");
    verifier_test_step.dependOn(&run_verifier_tests.step);

    // Verifier benchmarks
    const verifier_bench = b.addExecutable(.{
        .name = "verifier_bench",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/bench_runner.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
            },
        }),
    });
    b.installArtifact(verifier_bench);

    const run_verifier_bench = b.addRunArtifact(verifier_bench);
    run_verifier_bench.step.dependOn(b.getInstallStep());
    const bench_step = b.step("bench", "Run verifier benchmarks");
    bench_step.dependOn(&run_verifier_bench.step);

    // Integration tests (end-to-end prover-verifier)
    const integration_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/integration_tests.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "zigz", .module = zigz_mod },
                .{ .name = "hash-zig", .module = hash_zig_mod },
            },
        }),
    });
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
    all_tests_step.dependOn(rv64m_test_step);
    all_tests_step.dependOn(lasso_test_step);
    all_tests_step.dependOn(commit_test_step);
    all_tests_step.dependOn(vm_test_step);
    all_tests_step.dependOn(constraint_test_step);
    all_tests_step.dependOn(prover_test_step);
    all_tests_step.dependOn(verifier_test_step);
    all_tests_step.dependOn(integration_test_step);
}
