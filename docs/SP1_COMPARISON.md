# zigz vs SP1: Aligning Workflows and Running a Comparison

## Summary

**zigz** is a Jolt-style zkVM (sumcheck + Lasso + Merkle commitments); **SP1** is a STARK-based zkVM. Both prove RISC-V execution. This doc describes how to run zigz in an SP1-like way and how to compare them on the same workload.

---

## Differences Today

| Aspect | SP1 (Succinct) | zigz |
|--------|-----------------|------|
| **Proof system** | STARKs + FRI, Baby Bear | Sumcheck + Lasso, Baby Bear |
| **Program input** | RISC-V ELF (from Rust `cargo prove build`) | Raw `.bin` or **RISC-V ELF** (entry + PT_LOAD from file) |
| **Workflow** | `setup(ELF)` → `execute` / `prove` / `verify` via SDK or CLI | **CLI:** `zigz execute/prove/verify`; **build:** `zigz new` + `zigz build` |
| **CLI** | `cargo run -- --execute`, `--prove` | `zigz execute`, `zigz prove`, `zigz verify`, `zigz new`, `zigz build` |
| **Public I/O** | SP1Stdin / commit | Program hash, entry_pc, optional initial regs in proof |

---

## Making zigz Work Like SP1

### 1. SP1-like CLI

Provide the same mental workflow: **execute** (optional), **prove**, **verify**.

- **Execute only**  
  Run the VM on a program and print steps / result (no proof). Fast sanity check.

- **Prove**  
  `zigz prove <program.bin> [--entry 0x1000] [--max-steps N]`  
  Load program from file, run prover, print timing and proof size; optionally write proof to file.

- **Verify**  
  `zigz verify <proof.bin> <program.bin>`  
  Load proof and program, run verifier, print Accept/Reject and verify time.

Implementation options:

- Extend `src/main.zig` with subcommands and file I/O, or
- Add a dedicated `tools/zigz_cli.zig` (or `examples/zigz_cli.zig`) that uses the zigz library and is built as a separate executable.

### 2. Program Format

- **Today:** zigz expects **raw RISC-V instruction bytes** and an **entry PC** (e.g. `0x1000`). The VM loads that slice at the given address; no ELF parsing.
- **SP1:** Uses a full RISC-V ELF (e.g. from `cargo prove build`); entry point comes from the ELF header.

For a **fair comparison** you can:

- **Option A – Same source, two formats:**  
  - SP1: compile a Rust program to RISC-V ELF and run with SP1’s `execute` / `prove` / `verify`.  
  - zigz: extract the **.text** section from that ELF (or from a RISC-V `objcopy` binary) and pass it as `program` with the same effective entry (e.g. base where .text is loaded, often `0x1000` or the ELF entry).

- **Option B – Canonical micro-benchmark:**  
  Use a small, fixed sequence of instructions (e.g. NOPs or the add program from `integration_tests.zig`) and:
  - For SP1: compile a Rust program that does equivalent work (same number of steps / same logic).  
  - For zigz: use the same instruction bytes and entry_pc.

Option B is simpler for an apples-to-apples benchmark (same “program” in terms of steps and behavior).

### 3. Public Inputs / Compatibility

SP1 commits to public values (e.g. via `commit`). zigz currently binds **program hash**, **entry_pc**, and optional **initial registers** in the transcript. For a comparison you don’t need full SP1 compatibility; you only need to fix the **same logical “program”** (and optionally same public inputs) on both sides so that “proof of execution” is comparable.

---

## How to Run a Comparison

### Step 1: Define a Benchmark Program

- **Simple:** Use zigz’s `createAddProgram()` or `createNOPProgram(n)` from the integration tests. Save the bytes to `benchmark.bin` and use entry_pc `0x1000`.
- **SP1 side:** Either:
  - Compile a small Rust zkVM program that does the same work (e.g. same number of steps), or  
  - Use an SP1 example (e.g. Fibonacci) and, for zigz, replicate “same workload” with a hand-written or generated RISC-V snippet that matches step count / behavior as closely as possible.

### Step 2: Run zigz

```bash
# From the zigz repo (or use installed zigz binary)
zig build run -- prove benchmark.bin --entry 0x1000 --max-steps 1048576 --out proof.bin
zig build run -- prove program.elf --out proof.bin   # ELF: entry/segments from file

zig build run -- verify proof.bin benchmark.bin
zig build run -- verify proof.bin program.elf
```

Capture: **prove time**, **verify time**, **proof size** (and optionally memory).

### Step 3: Run SP1 on the Same Workload

```bash
# From an SP1 program directory (e.g. examples/fibonacci)
cargo prove build
RUST_LOG=info cargo run --release -- --execute   # optional
RUST_LOG=info cargo run --release -- --prove     # time this
# Verify (e.g. via SDK or script)
```

Capture the same metrics: **prove time**, **verify time**, **proof size**.

### Step 4: Compare

| Metric | zigz | SP1 |
|--------|------|-----|
| Prove time (s) | | |
| Verify time (ms) | | |
| Proof size (KB) | | |
| Steps / cycles | | |

Use the same machine and same “logical program” (same step count or same high-level task). Document: field (Baby Bear for both), proof system (Sumcheck+Lasso vs STARK), and whether SP1 uses compressed proof / recursion so the comparison is clear.

---

## Minimal CLI Sketch (for zigz)

To get “run like SP1” and “compare” quickly, add to `main.zig` (or a small CLI tool):

1. **Subcommands:** `execute`, `prove`, `verify`.
2. **Execute:** `zigz execute <program.bin> [--entry 0x1000] [--max-steps N]`  
   Load program, run VM (no proof), print step count and maybe final state.
3. **Prove:** `zigz prove <program.bin> [--entry 0x1000] [--max-steps N] [--out proof.bin]`  
   Load program, call `Prover(BabyBear).prove(...)`, serialize proof, print timing and size; optionally write `proof.bin`.
4. **Verify:** `zigz verify <proof.bin> <program.bin>`  
   Deserialize proof, load program, call `Verifier(BabyBear).verify(proof, program)`, print Accept/Reject and verify time.

Use the same entry_pc and max_steps as in integration tests (e.g. `0x1000`, `1 << 20`) so existing tests remain the reference.

---

## What's required for zigz to do the same (build + ELF workflow)

**Implemented.** zigz now has ELF loading, `zigz new`, and `zigz build`. See the main [README](../README.md#usage) for CLI usage and project workflow.


To match SP1’s “write program → build → prove” flow, zigz needs one or both of the following.

### 1. ELF loading in zigz (recommended)

**Goal:** Accept an ELF file so the user doesn’t have to pass raw `.bin` + `--entry` by hand.

**Required:**

- **ELF parser** (in zigz or a small dependency): read ELF headers and program headers.
- **Extract loadable segments** (at least `.text`): get the code bytes and their load address (e.g. `p_vaddr`).
- **Entry point:** read `e_entry` from the ELF header and use it as the initial PC.
- **CLI change:** if the input file has magic `0x7f 'E' 'L' 'F'`, treat it as ELF: parse it, set `program` = `.text` (or concatenate loadable segments in order), `entry_pc` = `e_entry`. Otherwise keep current behavior (raw `.bin` + `--entry`).

**Result:** User can run `zigz prove program.elf` (and optionally `zigz execute program.elf`) without running `objcopy` or looking up the entry point. Same ELF produced by SP1’s `cargo prove build` can be used with zigz after this.

**Note:** SP1 uses `riscv32im-succinct-zkvm-elf`; zigz’s VM is RV64. For running the same ELF in both, either zigz supports RV32 ELFs (decode/execute RV32) or you compare with a RV64 ELF / raw binary built for zigz.

---

### 2. A “build” step that produces the program (like `cargo prove build`)

**Goal:** From source code (Zig, C, or asm), produce something zigz can run: either an ELF (if 1. is done) or a `.bin` + entry point.

**Option A – Use Zig’s RISC-V target**

- Zig can emit RISC-V (e.g. `-target riscv64-linux` or `riscv32-freestanding`).
- **Required:** A `build.zig` (or script) that:
  1. Builds the program for the chosen RISC-V target (e.g. `zig build-exe -target riscv64-linux program.zig` or similar).
  2. Either:
     - Produces an ELF and (if 1. is done) zigz loads it, or
     - Runs `objcopy -O binary --only-section=.text program.elf program.bin` and prints or records the entry point (e.g. from `readelf -h` or a small ELF parse) so the user can pass `--entry` to zigz.

**Option B – External RISC-V toolchain (GCC/Clang)**

- **Required:** Install a RISC-V toolchain (e.g. `riscv64-unknown-elf-gcc` or `riscv32-unknown-elf-gcc`).
- Build: `riscv64-unknown-elf-gcc -nostdlib -static -o program.elf program.c`.
- Then either:
  - Use the ELF in zigz (if 1. is done), or
  - Run `objcopy -O binary --only-section=.text program.elf program.bin` and pass `program.bin` + `--entry <e_entry>` to zigz.
- Can be wrapped in a script or `build.zig` (e.g. `zig build program` runs the compiler + objcopy and writes `program.bin` + a small file with the entry point).

**Option C – “zigz new” + “zigz build” (SP1-style CLI)**

- **Required:**
  - **zigz new:** Create a project template (e.g. a Zig or C source and a `build.zig` / script that uses Option A or B).
  - **zigz build:** Run the build (Zig or external toolchain), produce ELF or `.bin` (+ entry), so the next step is `zigz prove <path>` (and optionally `zigz execute`).

**Result:** One command builds the program, another runs/proves it, similar to SP1’s `cargo prove build` and `cargo run -- --prove`.

---

### Summary

| Piece | Purpose |
|-------|--------|
| **ELF loading** | Use ELF (and `e_entry`) in zigz so you can `zigz prove program.elf` without manual `.bin` + `--entry`. |
| **Build step** | Turn source (Zig/C/asm) into RISC-V ELF or `.bin` + entry (Zig target, or GCC/Clang + optional script). |
| **Optional: zigz new/build** | Project template + single build command so the workflow matches SP1 (“new” → “build” → “execute”/“prove”). |

Doing **1 (ELF loading)** gives the biggest gain for reusing SP1-built ELFs or any RISC-V toolchain output. Adding **2 (build)** gives the full “write code → build → prove” flow.

---

## References

- SP1: [Succinct Docs](https://docs.succinct.xyz/docs/sp1/generating-proofs/basics), [GitHub](https://github.com/succinctlabs/sp1)
- zigz: Jolt-style (sumcheck + Lasso), see README and MODULES.md
