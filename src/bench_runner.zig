// Entry point for verifier_bench. Calls into the zigz lib so benchmarks.zig
// is compiled with lib.zig as root (path imports work) instead of as exe root.
const zigz = @import("zigz");
pub fn main() !void {
    return zigz.benchmarks.main();
}
