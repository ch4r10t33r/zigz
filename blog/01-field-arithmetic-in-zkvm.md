# Field Arithmetic: The Foundation of Zero-Knowledge Virtual Machines

*Part 1 of the zigz zkVM Deep Dive Series*

---

## Introduction

At the core of every zero-knowledge virtual machine sits a surprisingly
simple mathematical structure: the **finite field**.

Even though a zkVM performs fairly sophisticated cryptographic
computations to prove program execution, every single operation
eventually reduces to arithmetic inside a finite field. Addition,
polynomial evaluation, hashing, constraint checks. Everything happens
there.

While working on **zigz**, I ended up spending a lot of time thinking
about fields and how to implement them cleanly and efficiently in Zig.

In this post I'll walk through:

- What finite fields are and why they matter for zkVMs\
- How zigz implements generic field arithmetic in Zig\
- How to think about field selection for zkVMs\
- The fields zigz currently supports (BabyBear, Goldilocks, etc.)

By the end, the hope is that the importance of field choice becomes
clear and that Zig's compile-time generics start to look like a very
natural fit for this problem.

---

## What is a Finite Field?

A **finite field** (also known as a *Galois field*) is simply a set with
a finite number of elements where the usual arithmetic operations behave
nicely.

In other words, you can:

- add\
- subtract\
- multiply\
- divide (except by zero)

and the results always stay inside the set.

### A Simple Example: F₁₇

Take the field **F₁₇**, which is just the integers modulo 17.

```
Elements: {0,1,2,...,16}
Addition: (a + b) mod 17
Multiplication: (a × b) mod 17
```

Examples:

- `12 + 8 = 20 mod 17 = 3`
- `5 × 7 = 35 mod 17 = 1`
- `16 = -1 (mod 17)`

One important property is that **every non-zero element has a
multiplicative inverse**.

For instance:

```
5 × 7 = 1 mod 17
```

which means **7 is the inverse of 5** in this field.

---

### Prime Fields

The most commonly used finite fields in zk systems are **prime fields**,
written as **Fₚ**, where `p` is a prime number.

The elements are simply:

```
{0,1,2,...,p−1}
```

with arithmetic performed modulo `p`.

The requirement that `p` be prime is important. If the modulus were
composite, some elements would not have multiplicative inverses and the
structure would no longer be a field.

---

## Why zkVMs Use Finite Fields

Zero-knowledge proof systems rely heavily on finite fields for a few
reasons.

### 1. They Work Well for Cryptography

Many cryptographic assumptions live naturally in finite fields,
including problems like:

- discrete logarithms\
- polynomial identities\
- collision resistance in algebraic hash functions

These are the building blocks used in proof systems.

---

### 2. Exact Arithmetic

Field arithmetic is **exact**.

Unlike floating-point computations there are:

- no rounding errors\
- no platform-dependent behaviour\
- no precision loss

This matters a lot in zk systems because the **prover and verifier must
compute exactly the same values**.

---

### 3. Efficient CPU Arithmetic

When the field modulus is chosen carefully, arithmetic becomes extremely
efficient.

Modern CPUs handle 64-bit arithmetic very well, so primes that fit
nicely within 32 or 64 bits can be implemented with very little
overhead.

This allows:

- fast modular reduction\
- simple multiplication logic\
- efficient implementations in software

---

### 4. Polynomial Commitment Schemes

zkVMs make heavy use of **polynomials**.

For example:

- encoding execution traces\
- constraint systems\
- lookup arguments

Polynomials over finite fields behave very well mathematically. They
have unique representations and can be evaluated or interpolated
efficiently.

---

### 5. Sumcheck Protocols

Protocols like **sumcheck** (used heavily in systems such as Jolt) rely
on evaluating multilinear polynomials at random challenge points.

These operations only make sense if the underlying arithmetic is exact
and deterministic. Finite fields provide that structure.

---

## zigz's Field Implementation

When I started implementing field arithmetic in zigz, the goal was to
keep it:

- generic\
- efficient\
- type-safe

Zig's `comptime` feature turns out to be extremely convenient for this.

### Generic Field Type

```zig
pub fn Field(comptime T: type, comptime modulus: T) type {
    if (modulus <= 1) {
        @compileError("Field modulus must be greater than 1");
    }

    return struct {
        value: T,

        pub const MODULUS: T = modulus;
    };
}
```

The important part here is that the modulus is a **compile-time
parameter**.

That gives a few nice properties:

- zero runtime overhead\
- the compiler can specialize the code per field\
- different fields become different types

Which also means you **cannot accidentally mix them**.

---

### Addition

```zig
pub fn add(self: Self, other: Self) Self {
    const sum = @addWithOverflow(self.value, other.value);

    if (sum[1] == 1) {
        return Self{ .value = @mod(sum[0], MODULUS) };
    }

    if (sum[0] >= MODULUS) {
        return Self{ .value = sum[0] - MODULUS };
    }

    return Self{ .value = sum[0] };
}
```

The main idea is to handle overflow first and avoid a full modulo
operation whenever possible.

---

### Subtraction

```zig
pub fn sub(self: Self, other: Self) Self {
    if (self.value >= other.value) {
        return Self{ .value = self.value - other.value };
    }

    return Self{ .value = MODULUS - (other.value - self.value) };
}
```

This is just modular subtraction with a simple borrow correction.

---

### Multiplication

```zig
pub fn mul(self: Self, other: Self) Self {
    const wide_product = @as(u128, self.value) * @as(u128, other.value);
    const reduced = @mod(wide_product, MODULUS);
    return Self{ .value = @intCast(reduced) };
}
```

Here the multiplication is done in a wider integer type to avoid
overflow before the reduction step.

---

### Division

Division is implemented through multiplicative inverses.

```zig
pub fn inv(self: Self) !Self {
    if (self.isZero()) {
        return error.DivisionByZero;
    }

    // Extended Euclidean algorithm
}
```

Once the inverse is computed:

```
a / b = a × b⁻¹
```

---

## Choosing the Right Field

The choice of field has a real impact on zkVM performance.

zigz currently includes a few commonly used ones.

### BabyBear Field

```
p = 2³¹ − 2²⁷ + 1
```

```zig
pub const BabyBear = field.Field(u64, 2013265921);
```

Properties:

- fits comfortably within 31 bits\
- very fast arithmetic\
- widely used in STARK-style systems

This is currently the **default field used in zigz**.

---

### Goldilocks Field

```
p = 2⁶⁴ − 2³² + 1
```

```zig
pub const Goldilocks = field.Field(u64, 0xFFFFFFFF00000001);
```

This field is popular in systems like **Plonky2**.

Advantages include:

- good 64-bit performance\
- efficient reduction\
- large multiplicative subgroup

The name "Goldilocks" comes from the fact that it's **large enough for
security but still efficient to compute with**.

---

### Mersenne Fields

Examples:

```
2³¹ − 1
2⁶¹ − 1
```

These allow extremely efficient modular reduction using bit operations
rather than division.

---

## Why zigz Uses Compile-Time Specialization

One of the nicest things about Zig here is that we can write generic
code once and let the compiler specialize it.

Example:

```zig
const a = BabyBear.init(10);
const b = BabyBear.init(20);

const c = a.add(b);
```

If we switch fields:

```zig
const a = Goldilocks.init(10);
const b = Goldilocks.init(20);
```

the compiler produces a **separate optimized version** of the
arithmetic.

And since the types differ, this will not compile:

```zig
a_baby.add(b_gold)
```

which avoids a whole class of bugs.

---

## Where Fields Appear in zigz

Field arithmetic shows up almost everywhere in the system:

- constraint evaluation\
- polynomial evaluation\
- sumcheck protocol\
- lookup arguments

For example:

```zig
const prover = try Prover(BabyBear).init(allocator);
const proof = try prover.prove(trace);
```

Changing the field simply changes the arithmetic layer underneath.

---

## Final Thoughts

Finite field arithmetic is the mathematical foundation on which zkVMs
are built. Every higher-level component eventually reduces to operations
inside a field.

Some key points that stood out while building zigz:

- finite fields give us exact and deterministic arithmetic\
- the choice of field directly impacts prover performance\
- Zig's compile-time generics make field specialization
straightforward\
- strong typing prevents mixing incompatible fields

In the next post I'll move up one level and talk about **polynomials**,
particularly multilinear polynomials, and how they show up in zkVM
designs.

---

*Next: Polynomials in zkVMs*