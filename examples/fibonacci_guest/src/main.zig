/// Fibonacci guest program for the zigz zkVM.
///
/// This is the "program" side — the code that runs *inside* the VM.
/// It is the zigz equivalent of SP1's fibonacci program:
///   https://github.com/succinctlabs/sp1/blob/main/examples/fibonacci/program/src/main.rs
///
///   SP1 guest                        zigz guest
///   ────────────────────────         ────────────────────────
///   sp1_zkvm::io::read::<u32>()      io.read(u64)
///   sp1_zkvm::io::commit(&a)         io.commit(a)
///
/// The host provides n via the input tape; the guest commits fib(n) and
/// fib(n+1) to the output tape.  No inline assembly required.
const io = @import("zigz_io");

export fn _start() noreturn {
    const n = io.read(u64); // read n from the host input tape

    var a: u64 = 0; // fib(0)
    var b: u64 = 1; // fib(1)

    var i: u64 = 0;
    while (i < n) : (i += 1) {
        const c = a + b;
        a = b;
        b = c;
    }

    io.commit(a); // fib(n)   → proof.public_io.outputs[0]
    io.commit(b); // fib(n+1) → proof.public_io.outputs[1]

    // Halt the VM.
    asm volatile ("ebreak");
    unreachable;
}
