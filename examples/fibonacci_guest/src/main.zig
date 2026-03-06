/// Fibonacci guest program for the zigz zkVM.
///
/// This is the "program" side — the code that runs *inside* the VM.
/// It is the zigz equivalent of SP1's fibonacci program:
///   https://github.com/succinctlabs/sp1/blob/main/examples/fibonacci/program/src/main.rs
///
/// Compile targeting freestanding RISC-V (no OS, no libc):
///   zig build  →  zig-out/bin/fibonacci_guest  (RISC-V ELF)
///
/// The host (examples/fibonacci.zig) embeds this ELF at compile time,
/// loads it into the zkVM, and generates a cryptographic proof of execution.
///
/// Outputs (placed in RISC-V calling-convention registers before EBREAK):
///   a0 (x10) = fib(n)      e.g. fib(10) = 55
///   a1 (x11) = fib(n + 1)  e.g. fib(11) = 89
/// Number of Fibonacci iterations.
const N: u64 = 10;

/// Entry point for the freestanding binary.
/// No OS, no libc, no CRT — this function IS the whole program.
export fn _start() noreturn {
    var a: u64 = 0; // fib(0)
    var b: u64 = 1; // fib(1)

    var i: u64 = 0;
    while (i < N) : (i += 1) {
        const c = a + b;
        a = b;
        b = c;
    }

    // Place results in ABI return registers before halting.
    // a0 (x10) = fib(N), a1 (x11) = fib(N+1).
    // The host reads these from proof.public_io.final_regs[10] and [11].
    // No clobber list needed — ebreak halts the VM immediately.
    asm volatile (
        \\mv a0, %[fib_n]
        \\mv a1, %[fib_n1]
        \\ebreak
        :
        : [fib_n] "r" (a),
          [fib_n1] "r" (b),
    );
    unreachable;
}
