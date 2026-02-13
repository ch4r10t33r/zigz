/// Library root for zigz. Re-exports the public API used by examples and other consumers.

// Core primitives
pub const field = @import("core/field.zig");
pub const field_presets = @import("core/field_presets.zig");
pub const decomposition = @import("core/decomposition.zig");

// Polynomial operations
pub const multilinear = @import("poly/multilinear.zig");

// Proof system
pub const sumcheck_prover = @import("proofs/sumcheck_prover.zig");
pub const sumcheck_verifier = @import("proofs/sumcheck_verifier.zig");

// VM and constraints
pub const vm_state = @import("vm/state.zig");
pub const witness = @import("constraints/witness.zig");
pub const constraints = @import("constraints/builder.zig");

// Full prover
pub const prover = @import("prover/prover.zig");
pub const proof = @import("prover/proof.zig");
pub const serialization = @import("prover/serialization.zig");

// Convenience re-exports
pub const BabyBear = field_presets.BabyBear;
pub const Goldilocks = field_presets.Goldilocks;
pub const Decompose64to31 = decomposition.Decompose64to31;
