## Description

<!-- Provide a brief description of the changes in this PR -->

## Type of Change

- [ ] Bug fix (non-breaking change which fixes an issue)
- [ ] New feature (non-breaking change which adds functionality)
- [ ] Breaking change (fix or feature that would cause existing functionality to not work as expected)
- [ ] Security fix (addresses a security vulnerability)
- [ ] Performance improvement
- [ ] Documentation update
- [ ] Test addition/improvement

## Changes Made

<!-- List the main changes in this PR -->

-
-
-

## Testing

### Unit Tests
- [ ] All unit tests pass (`zig build test-all`)
- [ ] Added new tests for new functionality
- [ ] Updated existing tests if behavior changed

### Integration Tests
- [ ] All integration tests pass (`zig build test-integration`)
- [ ] Tested end-to-end prover-verifier workflow
- [ ] Verified proof serialization/deserialization

### Security Tests (CRITICAL)
**These tests MUST pass for all PRs:**

- [ ] Test 6: Tampered commitment rejection ✅
- [ ] Test 7: Opening claims binding (Jolt PR #981 fix) ✅
- [ ] Test 8: Public input binding ✅
- [ ] Test 5: Transcript determinism ✅

> ⚠️ **Security tests validate Fiat-Shamir vulnerability fixes. If any fail, the zkVM is compromised!**

## Checklist

- [ ] My code follows the project's style guidelines
- [ ] I have performed a self-review of my own code
- [ ] I have commented my code, particularly in hard-to-understand areas
- [ ] I have updated documentation to reflect changes
- [ ] My changes generate no new warnings
- [ ] I have added tests that prove my fix is effective or that my feature works
- [ ] New and existing unit tests pass locally with my changes
- [ ] Any dependent changes have been merged and published

## Fiat-Shamir Transcript Changes

**If your PR modifies transcript binding order, answer these:**

- [ ] Does this change affect `transcript.appendBytes()` call order?
- [ ] Does this change affect `transcript.appendFieldElement()` call order?
- [ ] Does this change affect `transcript.challenge()` call order?
- [ ] Have you verified prover and verifier use identical binding order?
- [ ] Have you added tests to verify transcript determinism?

> ⚠️ **Transcript binding order is security-critical! Any changes require extra scrutiny.**

## Performance Impact

<!-- If applicable, describe performance implications -->

- Proof size change:
- Prover time change:
- Verifier time change:

## Breaking Changes

<!-- List any breaking changes and migration path -->

None /

## Related Issues

<!-- Link to related issues -->

Fixes #
Related to #

## Additional Context

<!-- Add any other context about the PR here -->

---

## For Reviewers

**Security Review Required If:**
- [ ] Changes to `src/prover/prover.zig` (transcript binding)
- [ ] Changes to `src/verifier/verifier.zig` (transcript binding)
- [ ] Changes to `src/core/hash.zig` (Fiat-Shamir implementation)
- [ ] Changes to polynomial commitment scheme
- [ ] Changes to sumcheck or Lasso protocols

**Review Checklist:**
- [ ] All CI checks pass
- [ ] Security tests pass
- [ ] Code is well-documented
- [ ] No obvious security issues
- [ ] Performance is acceptable
- [ ] Breaking changes are justified and documented
