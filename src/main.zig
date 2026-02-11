const std = @import("std");
const hash_zig = @import("hash-zig");

pub fn main() !void {
    const stdout = std.io.getStdOut().writer();
    try stdout.print("zigz — a STARK prover & verifier\n", .{});
}

test "basic sanity" {
    try std.testing.expect(true);
}
