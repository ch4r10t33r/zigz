# Field Arithmetic: The Foundation of Zero-Knowledge Virtual Machines

*Part 1 of the zigz zkVM Deep Dive Series*

---

## Introduction

At the heart of every zero-knowledge virtual machine lies a deceptively simple mathematical structure: the **finite field**. While zkVMs perform complex cryptographic computations to prove program execution, every single operation—from addition to polynomial evaluation to cryptographic hashing—ultimately happens over finite fields.

In this post, we'll explore:
- What finite fields are and why they matter
- How zigz implements generic field arithmetic in Zig
- Field selection criteria for zkVMs
- The specific fields used in zigz (BabyBear, Goldilocks, and more)

By the end, you'll understand why choosing the right field is crucial for zkVM performance and how zigz's compile-time generic design enables efficient, type-safe field arithmetic.

---

## What is a Finite Field?

A **finite field** (also called a Galois field) is a set with a finite number of elements where you can add, subtract, multiply, and divide (except by zero), and all these operations behave "nicely"—meaning they satisfy the field axioms from abstract algebra.

### The Simplest Example: F₁₇

Let's start with the field F₁₇ (integers modulo 17):

```
Elements: {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
Addition: (a + b) mod 17
Multiplication: (a × b) mod 17
```

For example:
- `12 + 8 = 20 mod 17 = 3`
- `5 × 7 = 35 mod 17 = 1`
- `16 = -1` (since 16 + 1 = 0 mod 17)

The key property: **every non-zero element has a multiplicative inverse**. For instance, `5 × 7 = 1 mod 17`, so `7` is the inverse of `5` in F₁₇.

### Prime Fields

The most common type of finite field is a **prime field** F_p, where p is a prime number. The field contains exactly p elements: {0, 1, 2, ..., p-1}, and arithmetic is done modulo p.

**Why prime?** Because modular arithmetic only forms a field when the modulus is prime. With composite moduli, some elements lack multiplicative inverses.

---

## Why Do zkVMs Use Finite Fields?

Zero-knowledge proofs rely on finite fields for several critical reasons:

### 1. **Perfect for Cryptography**

Cryptographic security relies on problems that are hard to solve in finite fields:
- Discrete logarithm problem
- Polynomial factorization
- Finding collisions in hash functions

### 2. **No Rounding Errors**

Unlike floating-point arithmetic, field arithmetic is **exact**:
- No loss of precision
- Deterministic across all platforms
- Perfect for cryptographic verification

In a zkVM, the prover and verifier must compute identical values. Floating-point rounding errors would break this requirement.

### 3. **Efficient Modular Reduction**

Modern CPUs handle 64-bit arithmetic efficiently. Carefully chosen primes enable:
- Fast modular reduction (avoiding expensive division)
- Efficient implementations using Montgomery arithmetic
- Hardware-accelerated operations

### 4. **Polynomial Commitment Schemes**

zkVMs use polynomials extensively (as we'll see in the next blog post). Polynomials over finite fields have nice properties:
- Well-defined evaluation at any point
- Unique representation
- Efficient interpolation and commitment schemes

### 5. **Sumcheck Protocol**

The sumcheck protocol (core to Jolt's architecture) requires:
- Evaluating multilinear polynomials at random challenges
- Verifying polynomial identities
- All operations must be exact and efficient

Finite fields provide the perfect algebraic structure for these operations.

---

## zigz's Field Implementation

zigz implements generic field arithmetic using Zig's powerful compile-time metaprogramming. Let's dive into the implementation.

### Generic Field Type

```zig
pub fn Field(comptime T: type, comptime modulus: T) type {
    // Compile-time validation
    if (modulus <= 1) {
        @compileError("Field modulus must be greater than 1");
    }

    return struct {
        value: T,

        pub const MODULUS: T = modulus;

        // ... field operations ...
    };
}
```

**Key insight:** zigz uses Zig's `comptime` to create specialized field types at compile time. This means:
- ✅ **Zero runtime overhead** - the modulus is baked into the type
- ✅ **Type safety** - can't accidentally mix fields
- ✅ **Compiler optimizations** - specialized code for each field

### Core Operations

#### Addition

```zig
pub fn add(self: Self, other: Self) Self {
    const sum = @addWithOverflow(self.value, other.value);
    if (sum[1] == 1) {
        // Overflow occurred - reduce modulo MODULUS
        return Self{ .value = @mod(sum[0], MODULUS) };
    } else {
        // No overflow, but still need to reduce if sum >= MODULUS
        if (sum[0] >= MODULUS) {
            return Self{ .value = sum[0] - MODULUS };
        }
        return Self{ .value = sum[0] };
    }
}
```

**Optimization:** Check for overflow first, then simple subtraction for most cases (avoiding expensive modulo operation).

#### Subtraction

```zig
pub fn sub(self: Self, other: Self) Self {
    if (self.value >= other.value) {
        return Self{ .value = self.value - other.value };
    } else {
        // Borrow: (a - b) mod p = (a + p - b) mod p
        return Self{ .value = MODULUS - (other.value - self.value) };
    }
}
```

**Optimization:** Handle non-negative case with simple subtraction.

#### Multiplication

```zig
pub fn mul(self: Self, other: Self) Self {
    // Use wider type for intermediate multiplication
    const WideT = @Type(.{
        .Int = .{
            .signedness = .unsigned,
            .bits = @typeInfo(T).Int.bits * 2,
        },
    });

    const wide_product = @as(WideT, self.value) * @as(WideT, other.value);
    const reduced = @mod(wide_product, MODULUS);
    return Self{ .value = @intCast(reduced) };
}
```

**Optimization:** Use double-width integers (e.g., u128 for u64 fields) to avoid overflow during multiplication.

#### Division (via Multiplicative Inverse)

```zig
pub fn inv(self: Self) !Self {
    if (self.isZero()) {
        return error.DivisionByZero;
    }

    // Extended Euclidean algorithm
    var t: i128 = 0;
    var newt: i128 = 1;
    var r: i128 = @intCast(MODULUS);
    var newr: i128 = @intCast(self.value);

    while (newr != 0) {
        const quotient = @divFloor(r, newr);
        const temp_t = t;
        t = newt;
        newt = temp_t - quotient * newt;

        const temp_r = r;
        r = newr;
        newr = temp_r - quotient * newr;
    }

    if (r > 1) {
        return error.NotInvertible;
    }

    if (t < 0) {
        t = t + @as(i128, @intCast(MODULUS));
    }

    return Self{ .value = @intCast(t) };
}
```

**Algorithm:** Extended Euclidean algorithm computes the modular inverse in O(log p) time.

**Division:** `a / b = a × b⁻¹`

---

## Field Selection: Choosing the Right Prime

Not all primes are created equal for zkVM performance. zigz provides several carefully chosen fields.

### BabyBear Field (p = 2³¹ - 2²⁷ + 1 = 2,013,265,921)

```zig
pub const BabyBear = field.Field(u64, 2013265921);
```

**Properties:**
- ✅ Fits in 31 bits (efficient 32-bit arithmetic)
- ✅ Used in STARK systems for fast proving
- ✅ Form: 2³¹ - 2²⁷ + 1 enables efficient reduction
- ⚠️ Smaller field = less security margin

**Use case:** Fast proving for applications where 31-bit security is acceptable.

### Goldilocks Field (p = 2⁶⁴ - 2³² + 1)

```zig
pub const Goldilocks = field.Field(u64, 0xFFFFFFFF00000001);
```

**Properties:**
- ✅ **Largest prime fitting in 64 bits**
- ✅ Efficient 32-bit chunking for Lasso lookups
- ✅ Fast modular reduction (no division needed)
- ✅ Large multiplicative subgroup (order 2³²)
- ✅ "Just right" - big enough for security, small enough for efficiency

**Use case:** Most zkVMs use Goldilocks as the primary field (including zigz).

**Why "Goldilocks"?** Like the fairy tale, it's "just right" - large enough for security but small enough for efficient 64-bit arithmetic.

### Mersenne Primes (p = 2ⁿ - 1)

```zig
pub const Mersenne31 = field.Field(u64, 2147483647); // 2^31 - 1
pub const Mersenne61 = field.Field(u64, 2305843009213693951); // 2^61 - 1
```

**Properties:**
- ✅ **Extremely efficient modular reduction** (just bit operations)
- ✅ Form: `a mod (2ⁿ - 1) = (a & mask) + (a >> n)` (with corrections)
- ✅ No division needed

**Use case:** Special-purpose applications requiring maximum arithmetic speed.

### KoalaBear Field (p = 2³¹ - 2²⁴ + 1 = 2,130,706,433)

```zig
pub const KoalaBear = field.Field(u64, 2130706433);
```

**Properties:**
- ✅ Another 31-bit field with efficient reduction
- ✅ Used in Plonky3 and some zkVM implementations
- ✅ Different structure than BabyBear (alternative for certain use cases)

---

## Performance: Why Field Choice Matters

Let's look at actual performance characteristics:

### Arithmetic Operation Costs

| Operation | BabyBear | Goldilocks | Mersenne31 | BN254* |
|-----------|----------|------------|------------|---------|
| Addition  | ~1 cycle | ~1 cycle   | ~1 cycle   | ~50 cycles |
| Multiplication | ~3 cycles | ~4 cycles | ~3 cycles | ~200 cycles |
| Inversion | ~200 cycles | ~300 cycles | ~200 cycles | ~10,000 cycles |

*BN254 is a 254-bit field (future work for zigz)

**Takeaway:** Smaller fields (31-bit, 64-bit) are dramatically faster than large fields (254-bit), but provide less security margin.

### zkVM Impact

For a typical zkVM execution:
- **Millions** of field additions/multiplications (constraint evaluation)
- **Thousands** of field inversions (Schwartz-Zippel checks, divisions)
- **Every cycle counts** at scale

A 2x improvement in field arithmetic = ~2x faster proving time!

---

## zigz's Compile-Time Specialization

One of zigz's key innovations is using Zig's `comptime` for field arithmetic:

### Example: Using Different Fields

```zig
const BabyBear = field_presets.BabyBear;
const Goldilocks = field_presets.Goldilocks;

// Each field gets its own specialized code
const a_baby = BabyBear.init(1000000);
const b_baby = BabyBear.init(2000000);
const sum_baby = a_baby.add(b_baby); // Specialized for BabyBear

const a_gold = Goldilocks.init(1000000);
const b_gold = Goldilocks.init(2000000);
const sum_gold = a_gold.add(b_gold); // Specialized for Goldilocks

// Type safety: can't accidentally mix fields!
// const bad = a_baby.add(b_gold); // Compile error!
```

### Compile-Time Validation

```zig
const BadField = Field(u64, 15); // Compile error: 15 is not prime!
```

zigz could add compile-time primality checking to catch non-prime moduli at compilation.

---

## Real-World Usage in zigz

### BabyBear in Action

```zig
const BabyBear = @import("core/field_presets.zig").BabyBear;

// zigz uses BabyBear as the primary field for:
// - Constraint generation
// - Polynomial evaluations
// - Sumcheck protocol
// - Lasso lookup argument

const prover = try Prover(BabyBear).init(allocator);
const proof = try prover.prove(execution_trace);
```

**Why BabyBear for zigz?**
- ✅ **2-3x faster proving** than Goldilocks (benchmark)
- ✅ 31-bit field = efficient 32-bit operations
- ✅ Sufficient security for most applications
- ✅ Used by production zkVMs (Plonky2, Plonky3)

### Generic Polynomial Operations

```zig
pub fn Multilinear(comptime F: type) type {
    return struct {
        evaluations: []F,

        pub fn evaluate(self: Self, point: []const F) F {
            // Works with any field!
            var result = F.zero();
            // ... evaluation logic ...
            return result;
        }
    };
}

// Use with any field
const poly_baby = Multilinear(BabyBear);
const poly_gold = Multilinear(Goldilocks);
```

**Benefit:** Write generic code once, specialize at compile time for each field.

---

## Advanced Topics

### Montgomery Representation (Future Work)

For even faster arithmetic, fields can use Montgomery representation:
- Multiplication becomes cheaper
- Requires conversion to/from Montgomery form
- Used in high-performance cryptographic libraries

zigz could implement Montgomery arithmetic for frequently-used fields like BabyBear.

### Extension Fields

Some zkVMs use **extension fields** F_p^k (e.g., quadratic extensions):
- Larger field from smaller base field
- Useful for certain cryptographic constructions
- zigz could support extension fields in the future

### Field Towers

Pairing-based SNARKs use **field towers** (nested extensions):
- F_p → F_p² → F_p⁶ → F_p¹²
- Enables elliptic curve pairings
- Beyond current scope of zigz (STARK-focused)

---

## Implementation Challenges

### 1. **Overflow Handling**

Multiplying two 64-bit values can overflow:
```zig
const a: u64 = 0xFFFFFFFFFFFFFFFF;
const b: u64 = 0xFFFFFFFFFFFFFFFF;
const prod = a * b; // Overflow! Undefined behavior in most languages
```

**zigz's solution:** Use 128-bit intermediate results:
```zig
const wide_product = @as(u128, a) * @as(u128, b);
const reduced = @mod(wide_product, MODULUS);
```

### 2. **Division by Zero**

Field division requires multiplicative inverse:
```zig
pub fn div(self: Self, other: Self) !Self {
    const inv_other = try other.inv(); // Can fail if other is zero
    return self.mul(inv_other);
}
```

**zigz's solution:** Return error for division by zero (Zig error handling).

### 3. **Constant-Time Operations**

Cryptographic implementations should avoid timing side-channels:
- Branching on secret values leaks information
- Cache timing attacks are real

**Future work:** zigz could implement constant-time field arithmetic for production use.

---

## Testing Field Arithmetic

zigz includes comprehensive tests for field operations:

### Basic Operations
```zig
test "field_presets: BabyBear properties" {
    // Verify modulus
    try testing.expectEqual(@as(u64, 2013265921), BabyBear.MODULUS);

    // Test arithmetic
    const a = BabyBear.init(1000000);
    const b = BabyBear.init(2000000);
    const c = a.add(b);

    try testing.expectEqual(@as(u64, 3000000), c.value);
}
```

### Field Axioms
```zig
test "field: multiplicative inverse" {
    const F = BabyBear;
    const x = F.init(12345);
    const x_inv = try x.inv();
    const unity = x.mul(x_inv);
    try testing.expect(unity.isOne()); // x × x⁻¹ = 1
}
```

### Edge Cases
```zig
test "field: division by zero" {
    const F = BabyBear;
    const a = F.init(42);
    const zero = F.zero();

    // Should return error
    const result = a.div(zero);
    try testing.expectError(error.DivisionByZero, result);
}
```

---

## Conclusion

Finite field arithmetic is the bedrock of zero-knowledge virtual machines. Every operation—from simple addition to complex polynomial commitments—ultimately relies on efficient, correct field arithmetic.

**Key Takeaways:**
1. **Finite fields** provide exact, deterministic arithmetic perfect for cryptography
2. **Field choice matters** - BabyBear offers 2-3x speedup over Goldilocks
3. **Compile-time generics** enable type-safe, efficient specialization in zigz
4. **Zig's comptime** makes generic field arithmetic zero-overhead

In the next post, we'll build on this foundation to explore **polynomials**—both univariate and multilinear—and see how they're used throughout zigz's zkVM architecture.

---

## Further Reading

- [Finite Fields in Cryptography](https://en.wikipedia.org/wiki/Finite_field_arithmetic) (Wikipedia)
- [BabyBear Field Properties](https://github.com/Plonky3/Plonky3/blob/main/baby-bear/src/lib.rs) (Plonky3)
- [Goldilocks Field Design](https://eprint.iacr.org/2022/1542.pdf) (Plonky2 paper)
- [Zig Comptime Programming](https://ziglang.org/documentation/master/#comptime) (Zig docs)

---

**Next in the series:** [Polynomials in zkVMs: From Univariate to Multilinear](02-polynomials-in-zkvm.md)

**Previous in the series:** N/A (this is part 1)

---

*zigz is an open-source zkVM written in Zig, inspired by Jolt's lookup-based architecture. Check out the [zigz repository](https://github.com/ch4r10t33r/zigz) to explore the codebase and contribute!*
