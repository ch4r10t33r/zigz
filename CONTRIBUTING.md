# Contributing to zigz

Thank you for your interest in contributing to zigz! This document provides guidelines for contributing to the project.

## Code of Conduct

Be respectful, constructive, and professional in all interactions.

## Getting Started

1. Fork the repository
2. Clone your fork: `git clone https://github.com/YOUR_USERNAME/zigz.git`
3. Create a feature branch: `git checkout -b feature/your-feature-name`
4. Make your changes
5. Run tests: `./run_tests.sh all`
6. Commit and push
7. Open a Pull Request

## Development Setup

### Prerequisites

- **Zig 0.14.1** (required; the project does not support Zig 0.15.x)
- Git (for dependency management)
- Basic understanding of zero-knowledge proofs (recommended)

### Zig version (0.14.1 only)

All builds and tests must use **Zig 0.14.1**. The repo root contains `.zig-version` with `0.14.1` so tools like zigup use the correct version when you `cd` into the project.

- **If you see errors** like `no field named 'root_source_file'` or `no field or member function named 'addStaticLibrary'`, you are running Zig 0.15.x. Switch to 0.14.1.
- **To use 0.14.1:**  
  - With zigup: `zigup fetch 0.14.1` then `zigup 0.14.1` to set the default, or ensure `zig` in your PATH is 0.14.1 when in this repo.  
  - Or install the [0.14.1 tarball](https://ziglang.org/download/) and put that `zig` on your PATH.

### Building

```bash
# Build in debug mode
zig build

# Build optimized
zig build -Doptimize=ReleaseFast

# Run main executable
zig build run
```

### Testing

**IMPORTANT: All tests must pass before submitting a PR.**

```bash
# Quick: Run integration tests only
./run_tests.sh quick

# Complete: Run all tests
./run_tests.sh all

# Or use zig directly
zig build test-all          # All tests (recommended)
zig build test-integration  # Integration tests only
zig build test              # Unit tests only
```

## Testing Requirements

### Unit Tests

Each module should have comprehensive unit tests:

- **Coverage**: Aim for >80% code coverage
- **Edge cases**: Test boundary conditions and error paths
- **Documentation**: Each test should have a clear docstring

### Integration Tests

**All PRs must pass the 10 integration tests**, especially:

1. ✅ Basic end-to-end
2. ✅ Serialization roundtrip
3. ✅ Program hash verification
4. ✅ Various program sizes
5. ✅ **Transcript determinism** (security-critical)
6. ✅ **Tampered commitment** (security-critical)
7. ✅ **Opening claims binding** (security-critical - Jolt PR #981)
8. ✅ **Public input binding** (security-critical)
9. ✅ Proof size scaling
10. ✅ Performance benchmark

**Tests 5-8 are security-critical!** If any fail, the zkVM is compromised.

See [tests/README.md](tests/README.md) for detailed test documentation.

## Security-Critical Code

### Fiat-Shamir Transcript Binding

The most security-sensitive code is the **Fiat-Shamir transcript binding order** in:

- `src/prover/prover.zig` - Prover transcript binding
- `src/verifier/verifier.zig` - Verifier transcript binding
- `src/core/hash.zig` - Fiat-Shamir implementation

**Critical Rules:**

1. **Order matters**: Prover and verifier must use identical binding order
2. **Bind before challenge**: All data must be bound BEFORE deriving challenges
3. **Opening claims binding**: Claims must be bound before batching (Jolt PR #981 fix)
4. **Domain separation**: Use unique separators for each protocol phase

### Example: Correct Transcript Binding

```zig
// PHASE 1: Bind public inputs FIRST
self.transcript.appendBytes(&program_hash);
self.transcript.appendFieldElement(F, F.init(entry_pc));

// PHASE 2: Bind all commitments
self.transcript.appendBytes("POLY_COMMITMENTS");
for (commitments) |c| {
    self.transcript.appendBytes(&c.commitment);
}

// PHASE 3: Derive challenges (AFTER binding)
for (openings) |*opening| {
    opening.challenge = self.transcript.challenge(F);
}

// PHASE 4: Bind opening claims (CRITICAL!)
self.transcript.appendBytes("OPENING_CLAIMS");
for (openings) |opening| {
    self.transcript.appendFieldElement(F, opening.value);
}
```

**If you modify transcript binding order, you MUST:**
- Update both prover AND verifier
- Add tests to verify determinism
- Document the change in your PR
- Request security review

## Pull Request Guidelines

### Before Submitting

- [ ] All tests pass (`./run_tests.sh all`)
- [ ] Code is formatted consistently
- [ ] Documentation is updated
- [ ] Security-critical changes are clearly marked
- [ ] Commit messages are clear and descriptive

### PR Requirements

1. **Clear description**: Explain what and why
2. **Tests**: All existing tests pass, new tests for new features
3. **Documentation**: Update relevant docs
4. **No breaking changes**: Unless absolutely necessary and well-justified
5. **Security review**: Required for transcript, commitment, or proof system changes

### Commit Message Format

Use conventional commits format:

```
<type>(<scope>): <short summary>

<detailed description>

<footer>
```

**Types:**
- `feat`: New feature
- `fix`: Bug fix
- `test`: Test additions/improvements
- `docs`: Documentation updates
- `perf`: Performance improvements
- `refactor`: Code refactoring
- `security`: Security fixes

**Examples:**

```
feat(verifier): add batch verification for multiple proofs

Implements efficient batch verification that amortizes commitment
checks across multiple proofs.

Closes #123
```

```
security: fix opening claims binding (Jolt PR #981)

Critical fix for Fiat-Shamir vulnerability where opening claims
were not bound to transcript before deriving batching coefficients.

This prevents the linear system exploit described in:
https://osec.io/blog/2026-03-03-zkvms-unfaithful-claims/
```

## Code Style

### Zig Style Guidelines

- Follow Zig's standard formatting (use `zig fmt`)
- Use meaningful variable names
- Add docstrings for public functions
- Keep functions focused and small
- Prefer explicit over implicit

### Documentation Style

```zig
/// Brief one-line description
///
/// Detailed explanation of what the function does,
/// including any important invariants or security properties.
///
/// Parameters:
/// - param1: Description of first parameter
/// - param2: Description of second parameter
///
/// Returns: Description of return value
///
/// Example:
/// ```zig
/// const result = myFunction(42, "hello");
/// ```
pub fn myFunction(param1: i32, param2: []const u8) !Result {
    // Implementation
}
```

## Areas for Contribution

### High Priority

1. **Performance optimization**
   - Field arithmetic optimizations
   - Parallel polynomial evaluations
   - Merkle tree caching
   - Prover optimizations

2. **Extended ISA support**
   - RV64I (64-bit)
   - M extension (multiply/divide)
   - F extension (floating-point)
   - Compressed instructions (RV32C)

3. **Production hardening**
   - Better error messages
   - Fuzzing infrastructure
   - Security audit preparation
   - Proof compression

### Medium Priority

4. **Examples and documentation**
   - More example programs
   - Tutorial documentation
   - Architecture deep-dives
   - Performance analysis

5. **Tooling**
   - Better debugging tools
   - Proof visualization
   - Profiling utilities
   - Benchmarking suite expansion

### Low Priority (but welcome!)

6. **Integration**
   - Language bindings (Python, JavaScript)
   - Proof aggregation/recursion
   - Alternative commitment schemes (FRI, KZG)

## Security Vulnerability Reporting

**DO NOT open public issues for security vulnerabilities.**

If you discover a security issue:

1. Email: [Your security contact email]
2. Describe the vulnerability
3. Provide steps to reproduce
4. Wait for response before public disclosure

We will:
- Acknowledge within 48 hours
- Provide a fix timeline
- Credit you in the security advisory (unless you prefer anonymity)

## Questions?

- **General questions**: Open a GitHub Discussion
- **Bug reports**: Open a GitHub Issue
- **Security issues**: Email privately (see above)
- **Feature requests**: Open a GitHub Issue with `[Feature Request]` prefix

## License

By contributing to zigz, you agree that your contributions will be licensed under the same license as the project.

## References

### Helpful Resources

- [Jolt zkVM Paper](https://eprint.iacr.org/2023/1217)
- [Lasso Lookup Arguments](https://eprint.iacr.org/2023/1216)
- [Fiat-Shamir Transform](https://en.wikipedia.org/wiki/Fiat%E2%80%93Shamir_heuristic)
- [RISC-V ISA Specification](https://riscv.org/technical/specifications/)
- [Zig Language Reference](https://ziglang.org/documentation/master/)

### Security References

- [Jolt PR #981 - Opening Claims Fix](https://github.com/a16z/jolt/pull/981)
- [Unfaithful Claims Vulnerability](https://osec.io/blog/2026-03-03-zkvms-unfaithful-claims/)
- [Fiat-Shamir Security](https://eprint.iacr.org/2016/771.pdf)

---

Thank you for contributing to zigz! 🚀
