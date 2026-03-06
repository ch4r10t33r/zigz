/// zigz_io — Guest I/O primitives for zkVM programs.
///
/// Import this package in guest programs to communicate with the host:
///
///   const io = @import("zigz_io");
///
///   pub fn main() void {
///       const n = io.read(u64);   // read from host input tape
///       io.commit(fib(n));        // write to public output tape
///   }
///
/// This mirrors sp1_zkvm::io:
///
///   SP1                          zigz
///   ────────────────────────     ────────────────────────
///   sp1_zkvm::io::read::<T>()    zigz_io.read(T)
///   sp1_zkvm::io::commit(&v)     zigz_io.commit(v)
///
/// Protocol (RISC-V ECALL convention, a7 = syscall number):
///   ECALL_COMMIT = 1   a0 = value to append to the output tape
///   ECALL_READ   = 2   a0 ← next word from the input tape (0 if exhausted)
///
/// This file MUST be compiled for a freestanding RISC-V target (rv64im).
/// It cannot be imported by host programs.
const ECALL_COMMIT: u64 = 1;
const ECALL_READ: u64 = 2;

/// Commit a value to the public output tape.
///
/// The host receives these values in `proof.public_io.outputs` after proving.
/// Multiple commits append in call order.
pub fn commit(value: anytype) void {
    const T = @TypeOf(value);
    const raw: u64 = switch (@typeInfo(T)) {
        .int => @intCast(value),
        .comptime_int => @intCast(value),
        else => @compileError("zigz_io.commit: unsupported type " ++ @typeName(T)),
    };
    ecallCommit(raw);
}

/// Read the next value from the host input tape.
///
/// Returns 0 when the tape is exhausted (same as sp1_zkvm::io behaviour
/// on empty input).
pub fn read(comptime T: type) T {
    const raw = ecallRead();
    return switch (@typeInfo(T)) {
        .int => @truncate(raw),
        else => @compileError("zigz_io.read: unsupported type " ++ @typeName(T)),
    };
}

// ---------------------------------------------------------------------------
// RISC-V ECALL wrappers (inline asm)
// ---------------------------------------------------------------------------

fn ecallCommit(value: u64) void {
    asm volatile (
        \\ecall
        :
        : [val] "{a0}" (value),
          [nr] "{a7}" (ECALL_COMMIT),
    );
}

fn ecallRead() u64 {
    var result: u64 = undefined;
    asm volatile (
        \\ecall
        : [result] "={a0}" (result),
        : [nr] "{a7}" (ECALL_READ),
    );
    return result;
}
