
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

## Acknowledgement

While writing this post I found myself revisiting algebraic ideas that I had first learned many years ago in school.  
A special acknowledgement is due to my secondary school mathematics teacher **Ms. Karpagam Sundaram**, whose patient and clear teaching of algebra, linear equations, and quadratic equations left a lasting impression.  
Those early lessons made it surprisingly easy to reconnect with the mathematical foundations behind zero‑knowledge systems today.

---

## Why zk Systems Love Polynomials

Many zk constructions rely on a simple but powerful idea from algebra: the **Schwartz–Zippel lemma**.

**Lemma (informal):** If two distinct polynomials of degree d over a finite field F agree at a randomly chosen point r ∈ F, the probability that they agree is at most d / |F|, where |F| is the size of the field.

### What does this mean in practice?

Instead of comparing two polynomials coefficient by coefficient (which is expensive), we can do something clever:

1. Pick a random point `r` from the field F
2. Evaluate both polynomials at `r`
3. Compare the results

If they match, then with high probability the polynomials are identical. The probability of error is bounded by `d / |F|`.

**Example:**

Let `p(x) = 3 + 2x` and `q(x) = 1 + 2x`. Both are degree 1 polynomials over F_17.

Pick a random r = 5:

```
p(5) = 3 + 2*5 = 13 mod 17
q(5) = 1 + 2*5 = 11 mod 17
```

They differ, so we know the polynomials are not equal. If they had matched, we would still have a small chance of being wrong (≤ 1/17).

This trick shows up everywhere in zk systems:

- **PLONK:** Encodes constraints as polynomial identities
- **STARKs:** Represent execution traces as polynomials
- **Jolt / Lasso:** Use multilinear polynomials for lookup tables
- **Sumcheck:** Proves polynomial sums efficiently

Once you dig into a zkVM, you realize almost everything reduces to **polynomial operations**.

---

## Univariate Polynomials: The Classics

### Definition

A **univariate polynomial** is a polynomial in a single variable x:

```
p(x) = a₀ + a₁x + a₂x² + a₃x³ + ... + aₙxⁿ
```

Where:
- Coefficients `aᵢ` are elements of a field F
- Degree `n` is the highest power of x
- Can be evaluated at any point `r`: `p(r) = a₀ + a₁r + a₂r² + ...`

### Example in F₁₇

```
p(x) = 5 + 3x + 2x²

p(0) = 5
p(1) = 5 + 3 + 2 = 10
p(2) = 5 + 6 + 8 = 19 mod 17 = 2
p(3) = 5 + 9 + 18 = 32 mod 17 = 15
```

### zigz Implementation

```zig
pub fn Univariate(comptime F: type) type {
    return struct {
        coefficients: []F,
        allocator: std.mem.Allocator,

        const Self = @This();

        /// Evaluate polynomial at a point using Horner's method
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

**Horner’s Method Explained:**  
Horner’s method rewrites

```
p(x) = a₀ + a₁x + a₂x² + ... + aₙxⁿ
```

as

```
p(x) = a₀ + x*(a₁ + x*(a₂ + ... + x*aₙ))
```

This reduces multiplications dramatically and makes polynomial evaluation very efficient.

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

Example:

```
(5 + 3x) + (2 + x + 4x²) = 7 + 4x + 4x²
```

#### Multiplication

```zig
pub fn mul(self: Self, other: Self) !Self {
    const deg_self = self.degree();
    const deg_other = other.degree();
    const result_deg = deg_self + deg_other;
    const coeffs = try self.allocator.alloc(F, result_deg + 1);

    for (coeffs) |*c| c.* = F.zero();

    for (0..self.coefficients.len) |i| {
        for (0..other.coefficients.len) |j| {
            const prod = self.coefficients[i].mul(other.coefficients[j]);
            coeffs[i + j] = coeffs[i + j].add(prod);
        }
    }

    return Self{ .coefficients = coeffs, .allocator = self.allocator };
}
```

Complexity: `O(n·m)` for naive multiplication.

---

## Multilinear Polynomials: The zkVM Workhorse

### Definition

A **multilinear polynomial** in v variables is a polynomial where **each variable has degree at most 1**.

```
p(x₁, x₂, x₃) =
a₀ + a₁x₁ + a₂x₂ + a₃x₁x₂ + a₄x₃ + a₅x₁x₃ + a₆x₂x₃ + a₇x₁x₂x₃
```

Key properties:

- `2^v` coefficients for v variables
- Uniquely determined by evaluations on `{0,1}^v`
- Partial evaluation is efficient

### Example in F₁₇

For 2 variables:

```
p(x₁, x₂) = a₀₀ + a₁₀x₁ + a₀₁x₂ + a₁₁x₁x₂
```

Evaluations on `{0,1}²`:

```
p(0,0)=a₀₀
p(1,0)=a₀₀+a₁₀
p(0,1)=a₀₀+a₀₁
p(1,1)=a₀₀+a₁₀+a₀₁+a₁₁
```

Concrete example:

```
Evaluations: [5, 8, 12, 3]

p(x₁,x₂) = 5 + 7x₁ + 3x₂ + 10x₁x₂ (mod 17)
```

### zigz Implementation

```zig
pub fn Multilinear(comptime F: type) type {
    return struct {
        evaluations: []F,
        num_vars: usize,
        allocator: std.mem.Allocator,

        const Self = @This();
    };
}
```

**Key insight:** store **evaluations instead of coefficients**.

---

### Partial Evaluation

Binding variables one by one:

```
p(x₁,x₂,x₃)
→ bind x₁=r₁
→ p'(x₂,x₃)
→ bind x₂=r₂
→ p''(x₃)
→ bind x₃=r₃
→ constant
```

This makes **sumcheck extremely efficient**.

---

### Sumcheck Protocol

Sumcheck proves statements of the form:

> The sum of polynomial p(x₁,...,xᵥ) over `{0,1}ᵛ` equals C

Each round:

1. Extract a univariate polynomial
2. Verifier checks sums at 0 and 1
3. Verifier samples random challenge

zigz implements this using efficient **partial evaluation**.

---

### Lasso Lookup Argument

Lookup tables are represented as **multilinear polynomials over boolean hypercubes**.

Large tables are decomposed into chunks to reduce memory and improve verification efficiency.

---

### Real‑World Performance

| Operation | Univariate (n=1000) | Multilinear (v=10) |
|-----------|---------------------|--------------------|
| Evaluation | ~1,000 ops | ~10,240 ops |
| Addition | ~1,000 ops | ~1,024 ops |
| Partial bind | N/A | ~512 ops |

---

### When to Use Which?

**Univariate polynomials**

- polynomial commitments
- sumcheck rounds
- interpolation

**Multilinear polynomials**

- execution traces
- lookup tables
- witness polynomials

zigz uses both strategically.

---

### Advanced: Lagrange Basis

Two useful forms:

- **Univariate Lagrange basis** for interpolation
- **Multilinear Lagrange basis** for hypercube evaluations

---

### Implementation Challenges

1. Memory management for large evaluation tables  
2. Efficient cache access patterns  
3. Careful allocator usage in Zig

---

### Testing

Tests include:

- polynomial evaluation
- partial binding
- polynomial arithmetic

---

### Future Optimizations

- FFT for univariate multiplication
- Sparse multilinear representations
- SIMD acceleration

---

## Conclusion

Polynomials are the language of zero‑knowledge proofs.

1. **Univariate polynomials** support commitments and algebraic checks  
2. **Multilinear polynomials** model execution traces and lookup tables  
3. **Partial evaluation** enables efficient protocols like sumcheck  
4. **zigz leverages both representations** for performance

Next we will dive deeper into the **sumcheck protocol**.

---

## Further Reading

- https://people.cs.georgetown.edu/jthaler/multilinear-extensions.pdf
- https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf
- https://eprint.iacr.org/2023/1216.pdf
- https://eprint.iacr.org/2023/1217.pdf

---

**Previous in the series:** Field Arithmetic: The Foundation of zkVMs  
**Next in the series:** The Sumcheck Protocol

---

*zigz is an open‑source zkVM written in Zig inspired by Jolt.*  
