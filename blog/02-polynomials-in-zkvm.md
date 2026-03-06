# Polynomials in zkVMs: From Univariate to Multilinear

*Part 2 of the zigz zkVM Deep Dive Series*

---

## Introduction

If finite fields are the foundation of zkVMs, then **polynomials over finite fields** are the building blocks. Virtually every component of a zero-knowledge virtual machine—from constraint systems to commitment schemes to verification protocols—relies on polynomials in some form.

But not all polynomials are created equal. zkVMs use two distinct types:
1. **Univariate polynomials** - single-variable polynomials p(x)
2. **Multilinear polynomials** - multi-variable polynomials where each variable has degree ≤ 1

In this post, we'll explore:
- Why polynomials are central to zkVMs
- Univariate vs. multilinear polynomials: when to use each
- How zigz implements both types efficiently
- Real-world usage in sumcheck, Lasso, and constraint systems

By the end, you'll understand how polynomials power modern zkVM architectures like Jolt, and how zigz's generic implementation enables flexible, efficient polynomial operations.

---

## Why Polynomials?

Zero-knowledge proofs fundamentally rely on a simple but powerful property:

> **Schwartz-Zippel Lemma:** If two distinct polynomials p(x) and q(x) of degree d agree at a random point, the probability is at most d/|F|.

This means:
- **Equality checking:** To prove p = q, evaluate both at a random point r
- **Low error:** For large fields and bounded degrees, error probability is negligible
- **Succinct verification:** Check one evaluation instead of comparing all coefficients

This property underlies virtually every zkVM construction:
- **PLONK:** Arithmetic constraints as polynomial equations
- **STARKs:** Execution traces as polynomials
- **Jolt/Lasso:** Lookup tables as multilinear polynomials
- **Sumcheck:** Proving polynomial sums without computing them

---

## Univariate Polynomials: The Classics

### Definition

A **univariate polynomial** is a polynomial in a single variable x:

```
p(x) = a₀ + a₁x + a₂x² + a₃x³ + ... + aₙxⁿ
```

Where:
- Coefficients `aᵢ` are field elements
- Degree is `n` (the highest power of x)
- Can be evaluated at any point: `p(r) = a₀ + a₁r + a₂r² + ...`

### Example in F₁₇

```
p(x) = 5 + 3x + 2x²

Evaluations:
p(0) = 5
p(1) = 5 + 3(1) + 2(1²) = 10
p(2) = 5 + 3(2) + 2(2²) = 5 + 6 + 8 = 19 mod 17 = 2
p(3) = 5 + 3(3) + 2(3²) = 5 + 9 + 18 = 32 mod 17 = 15
```

### zigz Implementation

```zig
pub fn Univariate(comptime F: type) type {
    return struct {
        /// Coefficients in increasing degree order: [a₀, a₁, a₂, ..., aₙ]
        coefficients: []F,
        allocator: std.mem.Allocator,

        const Self = @This();

        /// Evaluate polynomial at a point using Horner's method
        /// p(x) = a₀ + x(a₁ + x(a₂ + x(a₃ + ...)))
        /// Efficient: O(n) with n-1 multiplications
        pub fn evaluate(self: Self, x: F) F {
            if (self.coefficients.len == 0) return F.zero();

            // Horner's method: start from highest degree
            var result = self.coefficients[self.coefficients.len - 1];
            var i = self.coefficients.len - 1;
            while (i > 0) {
                i -= 1;
                result = result.mul(x).add(self.coefficients[i]);
            }
            return result;
        }
    };
}
```

**Key optimization:** Horner's method evaluates in O(n) time with n-1 multiplications instead of n(n+1)/2 for naive evaluation.

### Operations on Univariate Polynomials

#### Addition
```zig
pub fn add(self: Self, other: Self) !Self {
    const max_len = @max(self.coefficients.len, other.coefficients.len);
    const coeffs = try self.allocator.alloc(F, max_len);

    for (0..max_len) |i| {
        const a = if (i < self.coefficients.len) self.coefficients[i] else F.zero();
        const b = if (i < other.coefficients.len) other.coefficients[i] else F.zero();
        coeffs[i] = a.add(b);
    }

    return Self{ .coefficients = coeffs, .allocator = self.allocator };
}
```

Example: `(5 + 3x) + (2 + x + 4x²) = 7 + 4x + 4x²`

#### Multiplication
```zig
pub fn mul(self: Self, other: Self) !Self {
    const deg_self = self.degree();
    const deg_other = other.degree();
    const result_deg = deg_self + deg_other;
    const coeffs = try self.allocator.alloc(F, result_deg + 1);

    // Initialize to zero
    for (coeffs) |*c| c.* = F.zero();

    // Compute product using convolution
    for (0..self.coefficients.len) |i| {
        for (0..other.coefficients.len) |j| {
            const prod = self.coefficients[i].mul(other.coefficients[j]);
            coeffs[i + j] = coeffs[i + j].add(prod);
        }
    }

    return Self{ .coefficients = coeffs, .allocator = self.allocator };
}
```

**Complexity:** O(n·m) for naive multiplication (can be improved to O(n log n) with FFT).

---

## Multilinear Polynomials: The zkVM Workhorse

### Definition

A **multilinear polynomial** in v variables is a polynomial where **each variable has degree at most 1**:

```
p(x₁, x₂, x₃) = a₀ + a₁x₁ + a₂x₂ + a₃x₁x₂ + a₄x₃ + a₅x₁x₃ + a₆x₂x₃ + a₇x₁x₂x₃
```

Key properties:
- **2^v coefficients** for v variables (one per boolean assignment)
- **Uniquely determined** by evaluations on boolean hypercube {0,1}^v
- **Efficient partial evaluation** (binding variables one at a time)

### Why Multilinear for zkVMs?

Multilinear polynomials are perfect for zkVMs because:

1. **Boolean hypercube representation** - execution traces are naturally indexed by bit strings
2. **Efficient sumcheck** - sum over boolean hypercube is just summing evaluations
3. **Sparse representations** - many zkVM polynomials are sparse
4. **Tensor products** - easy to compose multilinear polynomials

### Example in F₁₇

For 2 variables (x₁, x₂), a multilinear polynomial has 2² = 4 terms:

```
p(x₁, x₂) = a₀₀ + a₁₀x₁ + a₀₁x₂ + a₁₁x₁x₂
```

Represented by evaluations on {0,1}²:
```
p(0, 0) = a₀₀
p(1, 0) = a₀₀ + a₁₀
p(0, 1) = a₀₀ + a₀₁
p(1, 1) = a₀₀ + a₁₀ + a₀₁ + a₁₁
```

**Concrete example:**
```
Evaluations: [5, 8, 12, 3]
Means: p(0,0)=5, p(0,1)=8, p(1,0)=12, p(1,1)=3

What's the polynomial?
p(x₁, x₂) = 5 + 7x₁ + 3x₂ + 10x₁x₂ (in F₁₇)
```

### zigz Implementation

```zig
pub fn Multilinear(comptime F: type) type {
    return struct {
        /// Evaluations on boolean hypercube {0,1}^v
        /// Length must be a power of 2: evaluations.len = 2^num_vars
        /// Index i corresponds to binary representation of (x_v-1, ..., x_1, x_0)
        evaluations: []F,
        num_vars: usize,
        allocator: std.mem.Allocator,

        const Self = @This();
    };
}
```

**Key insight:** Store evaluations, not coefficients. This is more efficient for zkVM operations.

### Boolean Hypercube Indexing

For a 3-variable polynomial, evaluations are indexed:

```
Index | Binary | (x₂, x₁, x₀) | p(x₂, x₁, x₀)
------|--------|--------------|---------------
  0   |  000   |   (0,0,0)    | evaluations[0]
  1   |  001   |   (0,0,1)    | evaluations[1]
  2   |  010   |   (0,1,0)    | evaluations[2]
  3   |  011   |   (0,1,1)    | evaluations[3]
  4   |  100   |   (1,0,0)    | evaluations[4]
  5   |  101   |   (1,0,1)    | evaluations[5]
  6   |  110   |   (1,1,0)    | evaluations[6]
  7   |  111   |   (1,1,1)    | evaluations[7]
```

This indexing is **crucial** for efficient operations!

### Evaluation at Arbitrary Points

To evaluate p(r₁, r₂, ..., rᵥ) where rᵢ are arbitrary field elements:

```zig
pub fn evaluate(self: Self, point: []const F) F {
    std.debug.assert(point.len == self.num_vars);

    var result = F.zero();

    // Sum over all boolean evaluations
    for (0..self.evaluations.len) |i| {
        var term = self.evaluations[i];

        // Multiply by Lagrange basis polynomial for this point
        for (0..self.num_vars) |j| {
            const bit = (i >> @intCast(j)) & 1;
            if (bit == 1) {
                term = term.mul(point[j]);
            } else {
                term = term.mul(F.one().sub(point[j]));
            }
        }

        result = result.add(term);
    }

    return result;
}
```

**Complexity:** O(2^v · v) - exponential in number of variables!

This is why zkVMs use **partial evaluation** (binding one variable at a time).

---

## Partial Evaluation: The Sumcheck Secret Weapon

### The Problem

Evaluating a v-variate multilinear polynomial at an arbitrary point takes O(2^v) time. For v=20, that's over 1 million operations!

### The Solution: Partial Evaluation

**Bind variables one at a time**, reducing the number of variables by 1 each step:

```
p(x₁, x₂, x₃)
  → bind x₁=r₁ → p'(x₂, x₃) (2-variate)
  → bind x₂=r₂ → p''(x₃) (1-variate)
  → bind x₃=r₃ → p'''() (constant)
```

**Complexity:** Each binding is O(2^(v-i)), so total is O(v · 2^v) amortized.

### zigz Implementation

```zig
pub fn bindVariable(self: Self, r: F) !Self {
    const new_len = self.evaluations.len / 2;
    const new_evals = try self.allocator.alloc(F, new_len);

    // For each pair of evaluations that differ only in the bound variable:
    // new_eval = (1-r) * eval_0 + r * eval_1
    for (0..new_len) |i| {
        const eval_0 = self.evaluations[2 * i];
        const eval_1 = self.evaluations[2 * i + 1];

        // Linear interpolation between the two points
        const one_minus_r = F.one().sub(r);
        new_evals[i] = one_minus_r.mul(eval_0).add(r.mul(eval_1));
    }

    return Self{
        .evaluations = new_evals,
        .num_vars = self.num_vars - 1,
        .allocator = self.allocator,
    };
}
```

**Key insight:** Linear interpolation between pairs of evaluations!

### Example

For p(x₁, x₂) with evaluations [5, 8, 12, 3], bind x₁ = 7:

```
Pairs differing only in x₁:
- p(0, 0) = 5 and p(1, 0) = 12
  → p'(0) = (1-7)·5 + 7·12 = -6·5 + 7·12 = -30 + 84 = 54

- p(0, 1) = 8 and p(1, 1) = 3
  → p'(1) = (1-7)·8 + 7·3 = -6·8 + 7·3 = -48 + 21 = -27

Result: p'(x₂) with evaluations [54, -27] (in the field)
```

---

## Sumcheck Protocol: Where It All Comes Together

The **sumcheck protocol** is the heart of Jolt's zkVM. It proves statements like:

> "The sum of polynomial p(x₁, ..., xᵥ) over the boolean hypercube {0,1}^v equals C"

### The Protocol

1. **Prover claims:** `∑_{x ∈ {0,1}^v} p(x) = C`
2. **Round i:** Prover sends univariate polynomial `gᵢ(Xᵢ)` claiming:
   ```
   gᵢ(Xᵢ) = ∑_{x_{i+1}, ..., x_v ∈ {0,1}} p(r₁, ..., r_{i-1}, Xᵢ, x_{i+1}, ..., x_v)
   ```
3. **Verifier checks:** `gᵢ(0) + gᵢ(1) = previous_claim`
4. **Verifier samples:** Random `rᵢ ← F`
5. **New claim:** `gᵢ(rᵢ)`

After v rounds, verify `p(r₁, ..., rᵥ)` via oracle query.

### Why Multilinear is Perfect Here

- **Partial evaluation:** Bind one variable per round
- **Univariate extraction:** Get `gᵢ(X)` from multilinear p by summing over remaining boolean assignments
- **Efficient:** Each round is O(2^(v-i)) operations

### zigz's Sumcheck Implementation

```zig
pub fn proveRound(
    state: *ProverState(F),
    round: usize,
) !UnivariateDensePolynomial(F) {
    // Extract univariate polynomial for this round
    // by summing over remaining boolean assignments

    const coeffs = try state.allocator.alloc(F, 2); // Degree 1 for multilinear
    coeffs[0] = F.zero();
    coeffs[1] = F.zero();

    // Sum over all evaluations, splitting by current variable
    for (0..state.polynomial.evaluations.len) |i| {
        const bit = (i >> @intCast(round)) & 1;
        if (bit == 0) {
            coeffs[0] = coeffs[0].add(state.polynomial.evaluations[i]);
        } else {
            coeffs[1] = coeffs[1].add(state.polynomial.evaluations[i]);
        }
    }

    // g(X) = coeffs[0]·(1-X) + coeffs[1]·X
    // Rearrange to standard form: g(X) = a₀ + a₁X
    const a0 = coeffs[0];
    const a1 = coeffs[1].sub(coeffs[0]);

    return try UnivariateDensePolynomial(F).init(
        state.allocator,
        &[_]F{ a0, a1 }
    );
}
```

---

## Lasso Lookup Argument: Multilinear Decomposition

Jolt's **Lasso** lookup argument uses multilinear polynomials to prove that all lookups in a table are valid.

### The Setup

1. **Lookup table:** T = [t₀, t₁, ..., t_{2^c - 1}] (size 2^c)
2. **Queries:** Q = [q₀, q₁, ..., q_{n-1}] (n queries into T)
3. **Goal:** Prove all qᵢ ∈ T efficiently

### Multilinear Representation

Represent T as a multilinear polynomial T̃(x₁, ..., x_c):
```
T̃(b₁, ..., b_c) = T[∑ᵢ bᵢ·2^i]  for bᵢ ∈ {0, 1}
```

**Why?** Boolean hypercube {0,1}^c naturally indexes table entries!

### Decomposition

For large tables (e.g., 2^32 entries), store as **decomposed lookups**:
```
T = T_high ⊗ T_low  (tensor product)

Where:
T_high: 2^16 entries (high 16 bits)
T_low: 2^16 entries (low 16 bits)
```

**Savings:** 2^16 + 2^16 = 131,072 vs. 2^32 = 4,294,967,296 entries!

### zigz Implementation

```zig
pub fn decomposeTable(
    allocator: std.mem.Allocator,
    table: []const F,
    chunk_bits: usize,
) ![]Multilinear(F) {
    const num_chunks = (table.len + (1 << chunk_bits) - 1) / (1 << chunk_bits);
    const chunks = try allocator.alloc(Multilinear(F), num_chunks);

    for (0..num_chunks) |i| {
        const start = i * (1 << chunk_bits);
        const end = @min(start + (1 << chunk_bits), table.len);
        chunks[i] = try Multilinear(F).init(allocator, table[start..end]);
    }

    return chunks;
}
```

---

## Real-World Performance

### Benchmark: Univariate vs. Multilinear

| Operation | Univariate (n=1000) | Multilinear (v=10, 2^10=1024) |
|-----------|---------------------|-------------------------------|
| Evaluation | ~1,000 ops | ~10,240 ops (naive) |
| Addition | ~1,000 ops | ~1,024 ops |
| Partial bind | N/A | ~512 ops |

**Takeaway:** Multilinear is expensive to evaluate fully but efficient for partial binding.

### Memory Footprint

For 1 million evaluations (v ≈ 20):
- **Multilinear:** 1M field elements (direct storage)
- **Univariate (degree 1M):** 1M field elements (coefficients)
- **Univariate (sparse):** Can be much smaller with clever representation

---

## When to Use Which?

### Use Univariate Polynomials When:
- ✅ Single-variable polynomials (sumcheck round polynomials)
- ✅ Polynomial commitments (FRI, KZG)
- ✅ Interpolation from points
- ✅ Degree bounds matter

### Use Multilinear Polynomials When:
- ✅ Execution traces (indexed by step/memory address)
- ✅ Lookup tables (indexed by input bits)
- ✅ Sumcheck protocol (partial evaluation)
- ✅ Constraint systems (witness polynomials)

### zigz's Approach

zigz uses **both**:
- **Multilinear:** Execution traces, lookup tables, witness polynomials
- **Univariate:** Sumcheck round polynomials, commitment openings

This hybrid approach leverages the strengths of each representation.

---

## Advanced: Lagrange Basis

Both representations can use **Lagrange basis**:

### Univariate Lagrange

For points (x₀, y₀), ..., (xₙ, yₙ), the Lagrange interpolating polynomial is:
```
p(x) = ∑ᵢ yᵢ · Lᵢ(x)

Where Lᵢ(x) = ∏_{j≠i} (x - xⱼ) / (xᵢ - xⱼ)
```

### Multilinear Lagrange

For the boolean hypercube, the Lagrange basis is:
```
L_b(x) = ∏ᵢ (xᵢ·bᵢ + (1-xᵢ)·(1-bᵢ))

Where b = (b₁, ..., bᵥ) ∈ {0,1}^v
```

This is exactly what we use in multilinear evaluation!

---

## Implementation Challenges

### 1. **Memory Management**

Multilinear polynomials can be huge (2^v evaluations):
```zig
// v=20 → 1 million u64 field elements → 8 MB
// v=30 → 1 billion u64 field elements → 8 GB
```

**zigz's solution:** Use Zig's allocator pattern for explicit memory management.

### 2. **Numerical Stability**

Not an issue for finite fields (exact arithmetic), but important when simulating with floats during development.

### 3. **Cache Efficiency**

Accessing evaluations in memory order matters:
```zig
// Good: sequential access
for (0..poly.evaluations.len) |i| {
    sum = sum.add(poly.evaluations[i]);
}

// Bad: random access (cache misses)
for (0..poly.evaluations.len) |i| {
    sum = sum.add(poly.evaluations[random_index[i]]);
}
```

---

## Testing Polynomials

### Univariate Tests
```zig
test "univariate: evaluate at point" {
    const F = BabyBear;
    // p(x) = 1 + 2x + 3x²
    const coeffs = [_]F{
        F.init(1),
        F.init(2),
        F.init(3),
    };
    const poly = try Univariate(F).init(testing.allocator, &coeffs);
    defer poly.deinit();

    // p(5) = 1 + 2·5 + 3·25 = 1 + 10 + 75 = 86
    const result = poly.evaluate(F.init(5));
    try testing.expectEqual(@as(u64, 86), result.value);
}
```

### Multilinear Tests
```zig
test "multilinear: partial evaluation" {
    const F = BabyBear;
    // p(x₁, x₂) with evaluations [1, 2, 3, 4]
    const evals = [_]F{
        F.init(1), // p(0,0)
        F.init(2), // p(0,1)
        F.init(3), // p(1,0)
        F.init(4), // p(1,1)
    };
    var poly = try Multilinear(F).init(testing.allocator, &evals);
    defer poly.deinit();

    // Bind x₁ = 0 (should get [1, 2])
    var bound = try poly.bindVariable(F.zero());
    defer bound.deinit();

    try testing.expectEqual(@as(usize, 1), bound.num_vars);
    try testing.expectEqual(@as(u64, 1), bound.evaluations[0].value);
    try testing.expectEqual(@as(u64, 2), bound.evaluations[1].value);
}
```

---

## Future Optimizations

### 1. **FFT for Univariate Multiplication**

Currently O(n²), can be O(n log n) with Fast Fourier Transform:
```zig
pub fn mulFFT(self: Self, other: Self) !Self {
    // TODO: Implement FFT-based multiplication
    // Requires NTT (Number Theoretic Transform) for finite fields
}
```

### 2. **Sparse Multilinear Representation**

Many zkVM polynomials are sparse (mostly zeros):
```zig
pub const SparseMultilinear(comptime F: type) = struct {
    /// Only store non-zero evaluations
    entries: std.AutoHashMap(usize, F),
    num_vars: usize,
};
```

### 3. **SIMD Acceleration**

Vectorize operations on evaluations:
```zig
// Process 4 field elements at once
const vec_a = @Vector(4, u64){ a[0], a[1], a[2], a[3] };
const vec_b = @Vector(4, u64){ b[0], b[1], b[2], b[3] };
const vec_sum = vec_a + vec_b; // SIMD add
```

---

## Conclusion

Polynomials are the language of zero-knowledge proofs. Understanding univariate and multilinear polynomials—and when to use each—is essential for building efficient zkVMs.

**Key Takeaways:**
1. **Univariate polynomials** are single-variable, used for commitments and round polynomials
2. **Multilinear polynomials** are multi-variable (degree 1 per variable), perfect for execution traces
3. **Partial evaluation** makes multilinear sumcheck efficient
4. **zigz uses both** types strategically throughout the zkVM

In the next post, we'll explore the **sumcheck protocol** in depth, seeing how it uses multilinear polynomials to enable efficient zero-knowledge proofs of execution.

---

## Further Reading

- [Multilinear Polynomials in Cryptography](https://people.cs.georgetown.edu/jthaler/multilinear-extensions.pdf) (Justin Thaler)
- [Sumcheck Protocol Explained](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) (Thaler's textbook, Chapter 4)
- [Lasso Lookup Arguments](https://eprint.iacr.org/2023/1216.pdf) (Lasso paper)
- [Jolt Architecture](https://eprint.iacr.org/2023/1217.pdf) (Jolt paper)

---

**Next in the series:** [The Sumcheck Protocol: Verifying Polynomial Sums Without Computing Them](03-sumcheck-protocol.md)

**Previous in the series:** [Field Arithmetic: The Foundation of zkVMs](01-field-arithmetic-in-zkvm.md)

---

*zigz is an open-source zkVM written in Zig, inspired by Jolt's lookup-based architecture. Check out the [zigz repository](https://github.com/ch4r10t33r/zigz) to explore the codebase and contribute!*
