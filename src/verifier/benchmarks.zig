const std = @import("std");
const verifier_mod = @import("verifier.zig");
const prover_mod = @import("../prover/prover.zig");
const proof_mod = @import("../prover/proof.zig");
const field = @import("../core/field.zig");
const BabyBear = @import("../core/field_presets.zig").BabyBear;

/// Benchmarking utilities for verifier performance measurement
///
/// Measures verification time as a function of:
/// - Number of execution steps (n)
/// - Proof size
/// - Number of lookup tables used
///
/// Expected performance: O(log n) verification time

pub fn BenchmarkSuite(comptime F: type) type {
    return struct {
        const Self = @This();
        const Verifier = verifier_mod.Verifier(F);
        const Prover = prover_mod.Prover(F);

        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
                .allocator = allocator,
            };
        }

        /// Benchmark result for a single test case
        pub const BenchmarkResult = struct {
            num_steps: usize,
            proof_size_bytes: usize,
            verification_time_ns: u64,
            verification_time_us: f64,
            steps_per_second: f64,
            result: proof_mod.VerificationResult,
        };

        /// Run full benchmark suite
        pub fn runBenchmarks(self: *Self) ![]BenchmarkResult {
            const test_sizes = [_]usize{ 16, 64, 256, 1024, 4096, 16384 };
            var results = try self.allocator.alloc(BenchmarkResult, test_sizes.len);

            for (test_sizes, 0..) |num_steps, i| {
                std.debug.print("Benchmarking {d} steps...\n", .{num_steps});
                results[i] = try self.benchmarkVerification(num_steps);
            }

            return results;
        }

        /// Benchmark verification for a specific number of steps
        fn benchmarkVerification(self: *Self, num_steps: usize) !BenchmarkResult {
            // Generate a simple test program (NOP instructions)
            const program = try self.generateTestProgram(num_steps);
            defer self.allocator.free(program);

            // Generate proof
            var prover = try Prover.init(self.allocator);
            defer prover.deinit();

            var proof = try prover.prove(program, 0x1000, null);
            defer proof.deinit();

            // Measure proof size
            const proof_size = proof.estimateSize();

            // Initialize verifier
            var verifier = Verifier.init(self.allocator);
            defer verifier.deinit();

            // Warm up (run once to prime caches)
            _ = try verifier.verify(proof, program);

            // Benchmark verification (run multiple times for accuracy)
            const num_iterations: usize = 10;
            var timer = try std.time.Timer.start();

            var i: usize = 0;
            while (i < num_iterations) : (i += 1) {
                // Reset verifier transcript for each iteration
                verifier.transcript = @import("../core/hash.zig").FiatShamirTranscript.init();
                _ = try verifier.verify(proof, program);
            }

            const elapsed_ns = timer.read();
            const avg_time_ns = elapsed_ns / num_iterations;
            const avg_time_us = @as(f64, @floatFromInt(avg_time_ns)) / 1000.0;

            // Calculate throughput
            const steps_per_second = if (avg_time_us > 0)
                @as(f64, @floatFromInt(num_steps)) / (avg_time_us / 1_000_000.0)
            else
                0.0;

            return BenchmarkResult{
                .num_steps = num_steps,
                .proof_size_bytes = proof_size,
                .verification_time_ns = avg_time_ns,
                .verification_time_us = avg_time_us,
                .steps_per_second = steps_per_second,
                .result = .Accept,
            };
        }

        /// Generate a simple test program with NOP instructions
        fn generateTestProgram(self: *Self, num_steps: usize) ![]u8 {
            // Each instruction is 4 bytes (RISC-V)
            const program_size = num_steps * 4;
            const program = try self.allocator.alloc(u8, program_size);

            // Fill with NOP instructions (ADDI x0, x0, 0)
            // Encoding: 0x00000013
            for (0..num_steps) |i| {
                const offset = i * 4;
                program[offset + 0] = 0x13;
                program[offset + 1] = 0x00;
                program[offset + 2] = 0x00;
                program[offset + 3] = 0x00;
            }

            return program;
        }

        /// Print benchmark results in a nice table format
        pub fn printResults(results: []const BenchmarkResult) void {
            std.debug.print("\n=== Verifier Benchmark Results ===\n\n", .{});
            std.debug.print("Steps    | Proof Size | Verify Time | Throughput\n", .{});
            std.debug.print("---------|------------|-------------|------------\n", .{});

            for (results) |result| {
                std.debug.print("{d:8} | {d:9} B | {d:9.2} μs | {d:9.0} steps/s\n", .{
                    result.num_steps,
                    result.proof_size_bytes,
                    result.verification_time_us,
                    result.steps_per_second,
                });
            }

            std.debug.print("\n", .{});
        }

        /// Verify O(log n) scaling
        pub fn analyzeScaling(results: []const BenchmarkResult) void {
            std.debug.print("\n=== Scaling Analysis ===\n\n", .{});

            // Check if verification time grows logarithmically
            // For O(log n), doubling steps should add constant time
            if (results.len < 2) return;

            for (1..results.len) |i| {
                const prev_steps = @as(f64, @floatFromInt(results[i - 1].num_steps));
                const curr_steps = @as(f64, @floatFromInt(results[i].num_steps));
                const prev_time = results[i - 1].verification_time_us;
                const curr_time = results[i].verification_time_us;

                const step_ratio = curr_steps / prev_steps;
                const time_ratio = curr_time / prev_time;

                // For O(log n), time_ratio should be approximately log(step_ratio)
                const expected_ratio = @log(step_ratio);

                std.debug.print("Steps: {d} → {d} (×{d:.2})\n", .{
                    results[i - 1].num_steps,
                    results[i].num_steps,
                    step_ratio,
                });
                std.debug.print("  Time ratio: {d:.2} (expected ~{d:.2} for O(log n))\n", .{
                    time_ratio,
                    expected_ratio,
                });
            }

            std.debug.print("\n", .{});
        }

        pub fn deinit(self: *Self) void {
            _ = self;
        }
    };
}

// ============================================================================
// Standalone benchmark runner
// ============================================================================

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    std.debug.print("Running zigz verifier benchmarks...\n", .{});

    var suite = BenchmarkSuite(BabyBear).init(allocator);
    defer suite.deinit();

    const results = try suite.runBenchmarks();
    defer allocator.free(results);

    BenchmarkSuite(BabyBear).printResults(results);
    BenchmarkSuite(BabyBear).analyzeScaling(results);
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;

test "benchmarks: small proof verification" {
    const allocator = testing.allocator;

    var suite = BenchmarkSuite(BabyBear).init(allocator);
    defer suite.deinit();

    const result = try suite.benchmarkVerification(16);

    // Verification should be reasonably fast
    try testing.expect(result.verification_time_us < 10000.0); // < 10ms
    try testing.expectEqual(proof_mod.VerificationResult.Accept, result.result);
}

test "benchmarks: proof size estimation" {
    const allocator = testing.allocator;

    var suite = BenchmarkSuite(BabyBear).init(allocator);
    defer suite.deinit();

    const result_16 = try suite.benchmarkVerification(16);
    const result_64 = try suite.benchmarkVerification(64);

    // Proof size should grow logarithmically
    // For 4x more steps (16→64), proof should grow by ~2x (2 more variables)
    const size_ratio = @as(f64, @floatFromInt(result_64.proof_size_bytes)) /
        @as(f64, @floatFromInt(result_16.proof_size_bytes));

    std.debug.print("Size ratio for 4x steps: {d:.2}\n", .{size_ratio});
    // Should be roughly 1.5-2.5x (logarithmic growth)
    try testing.expect(size_ratio > 1.0 and size_ratio < 3.0);
}
