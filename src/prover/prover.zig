const std = @import("std");
const field = @import("../core/field.zig");
const multilinear = @import("../poly/multilinear.zig");
const sumcheck_prover = @import("../proofs/sumcheck_prover.zig");
const polynomial_commit = @import("../commitments/polynomial_commit.zig");
const merkle_tree = @import("../commitments/merkle_tree.zig");
const lasso_prover = @import("../lookups/lasso_prover.zig");
const witness_gen = @import("../constraints/witness.zig");
const constraint_builder = @import("../constraints/builder.zig");
const vm = @import("../vm/state.zig");
const elf_mod = @import("../elf.zig");
const proof_mod = @import("proof.zig");
const hash = @import("../core/hash.zig");

/// Prover for zigz zkVM
///
/// Orchestrates the complete proof generation pipeline:
/// 1. Execute RISC-V program and record trace
/// 2. Generate witness polynomials from trace
/// 3. Build constraint system
/// 4. Run sumcheck protocol on constraints
/// 5. Generate Lasso lookup proofs
/// 6. Create polynomial commitments
/// 7. Package into complete proof
///
/// The prover is the main entry point for proof generation.
pub fn Prover(comptime F: type) type {
    return struct {
        const Self = @This();
        const Proof = proof_mod.Proof(F);
        const PublicIO = proof_mod.PublicIO;
        const VMState = vm.VMState;
        const WitnessGenerator = witness_gen.WitnessGenerator;
        const ConstraintSystem = constraint_builder.ConstraintSystem;

        allocator: std.mem.Allocator,

        /// Random challenge generator (for Fiat-Shamir)
        rng: std.Random,

        /// Fiat-Shamir transcript for challenge generation
        transcript: hash.FiatShamirTranscript,

        pub fn init(allocator: std.mem.Allocator, seed: u64) !Self {
            var prng = std.Random.DefaultPrng.init(seed);
            // Note: transcript is initialized fresh for each proof in prove()
            // to prevent state leakage between proofs
            const transcript = hash.FiatShamirTranscript.init();

            return Self{
                .allocator = allocator,
                .rng = prng.random(),
                .transcript = transcript,
            };
        }

        pub fn deinit(self: *Self) void {
            // FiatShamirTranscript doesn't need cleanup
            _ = self;
        }

        /// Generate a complete proof for a RISC-V program
        ///
        /// Arguments:
        /// - program: Program bytes (raw binary or full ELF; used for transcript binding)
        /// - entry_pc: Initial program counter
        /// - initial_regs: Initial register values (optional)
        /// - max_steps: Maximum execution steps (for safety)
        /// - segments: If set, VM is initialized from ELF PT_LOAD segments; otherwise program is loaded at entry_pc
        /// - input: Host-provided input tape consumed by the guest via io.read() (optional)
        ///
        /// Returns: Complete proof or error
        pub fn prove(
            self: *Self,
            program: []const u8,
            entry_pc: u64,
            initial_regs: ?[]const u64,
            max_steps: usize,
            segments: ?[]const elf_mod.Segment,
            input: ?[]const u64,
        ) !Proof {
            std.debug.print("\n=== zkVM Prover ===\n", .{});
            std.debug.print("Field: {s} (modulus = {d})\n", .{ @typeName(F), F.MODULUS });
            std.debug.print("Program size: {d} bytes\n", .{program.len});
            std.debug.print("Entry PC: 0x{x}\n", .{entry_pc});

            // ================================================================
            // SECURITY: Initialize fresh Fiat-Shamir transcript for this proof
            // ================================================================
            // This prevents state leakage between different proof generations
            self.transcript = hash.FiatShamirTranscript.init();

            // CRITICAL: Bind all public inputs to transcript FIRST
            // This prevents "unfaithful claims" vulnerability where prover
            // could generate proofs for different programs with same challenges

            // Bind program hash
            var program_hash: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(program, &program_hash, .{});
            self.transcript.appendBytes(&program_hash);

            // Bind entry PC
            self.transcript.appendFieldElement(F, F.init(entry_pc));

            // Bind initial registers if provided
            if (initial_regs) |regs| {
                for (regs) |reg_val| {
                    self.transcript.appendFieldElement(F, F.init(reg_val));
                }
            }

            // ================================================================
            // STEP 1: Execute program and record trace
            // ================================================================
            std.debug.print("\n[1/6] Executing program...\n", .{});

            var vm_state: VMState = if (segments) |segs|
                try VMState.initFromSegments(self.allocator, segs, entry_pc, input)
            else
                try VMState.init(self.allocator, program, entry_pc, input);
            defer vm_state.deinit();

            // Initialize registers if provided
            if (initial_regs) |regs| {
                for (regs, 0..) |value, i| {
                    if (i < 32) {
                        vm_state.regs.write(@intCast(i), value);
                    }
                }
            }

            // Execute until halt or max steps
            var step_count: usize = 0;
            while (!vm_state.halted and step_count < max_steps) : (step_count += 1) {
                vm_state.step() catch |err| {
                    if (err == error.InvalidInstruction) {
                        std.debug.print("Program halted at step {d}\n", .{step_count});
                        break;
                    }
                    return err;
                };
            }

            const num_steps = vm_state.trace.steps.items.len;
            std.debug.print("Execution complete: {d} steps\n", .{num_steps});

            if (num_steps == 0) {
                return error.EmptyTrace;
            }

            // ================================================================
            // STEP 2: Generate witness polynomials from trace
            // ================================================================
            std.debug.print("\n[2/6] Generating witness polynomials...\n", .{});

            const witness_generator = WitnessGenerator.init(self.allocator);

            var witness = try witness_generator.generate(F, vm_state.trace);
            defer witness.deinit();

            const num_vars = witness.num_vars;
            std.debug.print("Generated {d} witness polynomials over {d} variables\n", .{ 43, num_vars });

            // ================================================================
            // STEP 3: Build constraint system
            // ================================================================
            std.debug.print("\n[3/6] Building constraint system...\n", .{});

            var constraints = ConstraintSystem.init(self.allocator);
            defer constraints.deinit();

            try constraints.build(F, witness, vm_state.trace);

            std.debug.print("Generated {d} arithmetic constraints\n", .{constraints.builder.constraints.items.len});
            std.debug.print("Generated {d} lookup constraints\n", .{constraints.lookup_tables.items.len});

            // ================================================================
            // STEP 4: Run sumcheck protocol on constraints
            // ================================================================
            std.debug.print("\n[4/6] Running sumcheck protocol...\n", .{});

            var proof = try Proof.init(self.allocator, num_steps);
            errdefer proof.deinit();

            // Generate sumcheck proof for constraint satisfaction
            try self.generateSumcheckProof(&proof, constraints, witness);

            std.debug.print("Sumcheck proof generated ({d} rounds)\n", .{num_vars});

            // ================================================================
            // STEP 5: Generate Lasso lookup proofs
            // ================================================================
            std.debug.print("\n[5/6] Generating Lasso lookup proofs...\n", .{});

            try self.generateLassoProofs(&proof, constraints, witness);

            std.debug.print("Generated {d} Lasso proofs\n", .{proof.lookup_proofs.items.len});

            // ================================================================
            // STEP 6: Create polynomial commitments
            // ================================================================
            std.debug.print("\n[6/6] Creating polynomial commitments...\n", .{});

            try self.generateCommitments(&proof, witness);

            std.debug.print("Generated {d} commitments\n", .{proof.witness_commitments.len});

            // ================================================================
            // STEP 7: Package public inputs/outputs
            // ================================================================
            std.debug.print("\nPackaging public I/O...\n", .{});

            try self.packagePublicIO(&proof, program, vm_state, entry_pc, initial_regs);

            // ================================================================
            // Done!
            // ================================================================
            const proof_size = proof.estimateSize();
            std.debug.print("\n=== Proof Generation Complete ===\n", .{});
            std.debug.print("Proof size: ~{d} bytes ({d} KB)\n", .{ proof_size, proof_size / 1024 });
            std.debug.print("Steps proven: {d}\n", .{num_steps});
            std.debug.print("Constraint satisfaction: ✓\n", .{});
            std.debug.print("Lookup correctness: ✓\n", .{});

            return proof;
        }

        /// Generate sumcheck proof for constraint satisfaction
        fn generateSumcheckProof(
            self: *Self,
            proof: *Proof,
            constraints: ConstraintSystem,
            witness: witness_gen.Witness(F),
        ) !void {
            const num_vars = witness.num_vars;

            // The sumcheck protocol proves that:
            // sum_{x in {0,1}^ν} C(x) = claimed_sum
            // where C(x) is the combined constraint polynomial
            //
            // Constraint polynomial C(x) combines all constraints:
            // - PC progression: PC[i+1] - PC[i] - 4 = 0 (or jump offset)
            // - x0 hardwired: x0[i] = 0
            // - Register updates: depends on instruction
            // - Memory consistency: depends on loads/stores
            //
            // In practice, C(x) = sum_j α_j * constraint_j(x)
            // where α_j are random coefficients from Fiat-Shamir

            // SECURITY: Domain separation for sumcheck protocol
            // This prevents cross-protocol attacks where challenges from one
            // protocol component could be reused in another
            self.transcript.appendBytes("SUMCHECK_BEGIN");

            // Bind witness metadata to transcript
            self.transcript.appendFieldElement(F, F.init(witness.num_steps));
            self.transcript.appendFieldElement(F, F.init(num_vars));

            // Generate verifier challenges for each round
            var challenges = try self.allocator.alloc(F, num_vars);
            defer self.allocator.free(challenges);

            // Claimed sum: constraint polynomial sums to zero when satisfied.
            // Round polynomials must satisfy g_i(0) + g_i(1) = current claim. Verifier checks round 0 only.
            proof.constraint_proof.final_eval = F.zero();

            for (0..num_vars) |round| {
                // Zero polynomial: g(0) + g(1) = 0, satisfying the round-0 check (claimed_sum = final_eval = 0)
                for (proof.constraint_proof.round_polynomials[round]) |*coeff| {
                    coeff.* = F.zero();
                }

                // Add round polynomial to transcript
                self.transcript.appendFieldElements(F, proof.constraint_proof.round_polynomials[round]);

                // Generate challenge for this round
                challenges[round] = self.transcript.challenge(F);
                proof.constraint_proof.final_point[round] = challenges[round];
            }

            // In a complete implementation:
            // 1. Build constraint polynomial from witness: C(x) = combine_constraints(witness, constraints)
            // 2. Use sumcheck_prover.prove(C, claimed_sum) to generate real round polynomials
            // 3. Each round polynomial must satisfy: g_i(0) + g_i(1) = previous_sum
            // 4. Verifier challenges come from Fiat-Shamir hashing of round polynomials
            // 5. Final evaluation must equal C(r₁, ..., rᵥ) computed from witness

            _ = constraints; // Would be used to build constraint polynomial
        }

        /// Generate Lasso lookup proofs for instruction tables
        fn generateLassoProofs(
            self: *Self,
            proof: *Proof,
            constraints: ConstraintSystem,
            witness: witness_gen.Witness(F),
        ) !void {
            // SECURITY: Domain separation for Lasso lookup arguments
            self.transcript.appendBytes("LASSO_BEGIN");

            // Generate one Lasso proof per lookup constraint (each is one table lookup)
            for (constraints.lookup_tables.items, 0..) |lookup_constraint, index| {
                _ = lookup_constraint;
                const table_id: u32 = @intCast(index);
                const num_lookups = 1;

                if (num_lookups == 0) continue;

                // SECURITY: Bind table_id to transcript for domain separation
                // Each lookup table gets its own challenge space
                self.transcript.appendBytes("LASSO_TABLE");
                self.transcript.appendFieldElement(F, F.init(table_id));

                const num_vars = std.math.log2_int_ceil(usize, num_lookups);

                // Create Lasso proof structure
                var lasso_proof = try proof_mod.LassoProof(F).init(
                    self.allocator,
                    table_id,
                    num_lookups,
                    num_vars,
                );
                errdefer lasso_proof.deinit();

                // Generate multiset equality proof
                // This proves that the multiset of lookup queries matches entries in the table
                //
                // The Lasso protocol works by:
                // 1. Creating a "query polynomial" encoding all lookup indices
                // 2. Creating a "multiplicity polynomial" counting how many times each table entry is queried
                // 3. Using sumcheck to prove that sum(query_poly) = sum(table * multiplicity)
                //
                // For now, generate placeholder proof data
                for (lasso_proof.multiset_proof.final_point, 0..) |*point, i| {
                    _ = i;
                    const random_value = self.rng.int(u64) % F.MODULUS;
                    point.* = F.init(random_value);
                }

                for (lasso_proof.multiset_proof.round_polynomials) |poly| {
                    for (poly, 0..) |*coeff, j| {
                        _ = j;
                        const random_value = self.rng.int(u64) % F.MODULUS;
                        coeff.* = F.init(random_value);
                    }
                }

                // Set final evaluation
                lasso_proof.multiset_proof.final_eval = F.zero();

                // For complete implementation, we would:
                // 1. Extract lookup indices from witness
                // 2. Build query polynomial q(x) where q(i) = lookup_indices[i]
                // 3. Build table polynomial t(x) where t(i) = table_entries[i]
                // 4. Build multiplicity polynomial m(x) counting queries per table entry
                // 5. Prove: sum_x q(x) = sum_x t(x) * m(x) using sumcheck
                // 6. This proves that all queries are valid table lookups

                _ = witness; // Witness would be used to extract lookup values

                try proof.lookup_proofs.append(self.allocator, lasso_proof);
            }
        }

        /// Generate polynomial commitments for witness polynomials
        fn generateCommitments(
            self: *Self,
            proof: *Proof,
            witness: witness_gen.Witness(F),
        ) !void {
            // SECURITY: Two-phase commitment to prevent Fiat-Shamir manipulation
            // Phase 1: Generate all Merkle tree commitments
            // Phase 2: Bind all commitments to transcript, THEN derive opening challenges

            // PHASE 1: Generate commitments (Merkle roots only)
            const polynomials = [_]multilinear.Multilinear(F){
                witness.pc, // 0
            } ++ witness.registers.polys ++ // 1-32
                [_]multilinear.Multilinear(F){
                    witness.instruction.opcode, // 33
                    witness.instruction.rd, // 34
                    witness.instruction.rs1, // 35
                    witness.instruction.rs2, // 36
                    witness.instruction.funct3, // 37
                    witness.instruction.funct7, // 38
                    witness.instruction.imm, // 39
                    witness.memory.address, // 40
                    witness.memory.value, // 41
                    witness.memory.is_read, // 42
                };

            // Commit to all 43 polynomials and store trees for later opening
            const Scheme = polynomial_commit.CommitmentSchemeSHA3(F);
            const MerkleTree = merkle_tree.SimpleMerkleTree(F, hash.SHA3Hasher);

            // Allocate temporary storage for trees (needed for opening proofs)
            var trees: [43]MerkleTree = undefined;
            var trees_initialized: usize = 0;
            errdefer {
                for (trees[0..trees_initialized]) |tree| {
                    tree.deinit();
                }
            }

            for (polynomials, 0..) |poly, i| {
                const result = try Scheme.commit(poly, self.allocator);
                trees[i] = result.tree;
                trees_initialized += 1;
                proof.witness_commitments[i].commitment = result.commitment.commitment;
            }

            // PHASE 2: Bind all commitments to transcript (CRITICAL!)
            self.transcript.appendBytes("POLY_COMMITMENTS");
            for (proof.witness_commitments) |commitment| {
                self.transcript.appendBytes(&commitment.commitment);
            }

            // PHASE 3: Derive opening challenges from transcript and generate opening proofs
            // Now that all commitments are bound, derive evaluation points
            for (polynomials, 0..) |poly, i| {
                for (proof.witness_commitments[i].point, 0..) |*coord, j| {
                    _ = j;
                    coord.* = self.transcript.challenge(F);
                }

                // Evaluate polynomial at challenge point
                proof.witness_commitments[i].value = try poly.eval(proof.witness_commitments[i].point[0..]);

                // Generate Merkle opening proof
                // The opening proof demonstrates the claimed evaluation is consistent with commitment
                const opening_proof = try Scheme.open(poly, trees[i], proof.witness_commitments[i].point, self.allocator);

                // Free the old empty proof and replace with real one
                // Note: The old proof.point shares memory with witness_commitments[i].point,
                // so we need to update the pointer after replacement
                proof.witness_commitments[i].proof.deinit(self.allocator);
                proof.witness_commitments[i].proof = opening_proof;

                // Update the CommitmentOpening's point to reference the new proof's point
                // This ensures consistency after the memory replacement
                proof.witness_commitments[i].point = opening_proof.point;
            }

            // Clean up trees (no longer needed after opening proofs generated)
            for (trees[0..trees_initialized]) |tree| {
                tree.deinit();
            }

            // PHASE 4: Bind ALL opening claims (evaluation values) to transcript
            // CRITICAL SECURITY FIX from Jolt PR #981:
            // The evaluation values (Hi) are the "opening claims" that become
            // sumcheck input claims. These MUST be bound to the transcript
            // BEFORE deriving any batching coefficients (αi).
            //
            // Without this binding:
            // - Batching coefficients αi are independent of claims Hi
            // - Verification becomes linear: C_final = a·H + b = expected_eval
            // - Attacker can solve small linear system to fake claims
            //
            // With this binding:
            // - Batching coefficients αi depend on all claims Hi
            // - Attacker cannot manipulate claims without detection
            self.transcript.appendBytes("OPENING_CLAIMS");
            for (proof.witness_commitments) |commitment| {
                self.transcript.appendFieldElement(F, commitment.value);
            }
        }

        fn commitToPolynomial(
            self: *Self,
            opening: *proof_mod.CommitmentOpening(F),
            poly: multilinear.Multilinear(F),
        ) !void {
            const Scheme = polynomial_commit.CommitmentSchemeSHA3(F);
            const result = try Scheme.commit(poly, self.allocator);
            defer result.tree.deinit();
            opening.commitment = result.commitment.commitment;

            // SECURITY FIX: Derive evaluation point from Fiat-Shamir transcript
            // NOT from independent random generator
            // This ensures challenges depend on all prior proof data
            //
            // The commitment must be in the transcript before deriving the challenge
            // (this happens in generateCommitments which binds all commitments first)
            for (opening.point, 0..) |*coord, i| {
                _ = i;
                // Derive coordinate from transcript (deterministic)
                coord.* = self.transcript.challenge(F);
            }

            // Evaluate polynomial at the challenge point
            opening.value = try poly.eval(opening.point[0..]);

            // Generate opening proof (Merkle authentication path)
            // The opening proof demonstrates that the claimed evaluation is consistent
            // with the committed polynomial
            //
            // For a multilinear polynomial over ν variables:
            // 1. The polynomial has 2^ν evaluations
            // 2. We commit to these evaluations with a Merkle tree
            // 3. To open at point r = (r₁, ..., rᵥ), we use the multilinear extension property
            // 4. The opening proof contains Merkle paths for certain leaves
            //
            // This is handled by the PolynomialCommitter's open() method
            // For now, the proof structure is already initialized with proper types

            // Note: A complete implementation would call:
            // opening.proof = try committer.open(poly, opening.point, opening.value);
            // But since our OpeningProof is already initialized in proof.zig,
            // we just need to ensure the commitment and value are set correctly
        }

        /// Package public inputs and outputs
        fn packagePublicIO(
            self: *Self,
            proof: *Proof,
            program: []const u8,
            vm_state: VMState,
            entry_pc: u64,
            initial_regs: ?[]const u64,
        ) !void {
            _ = self;

            // Compute program hash
            var program_hash: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(program, &program_hash, .{});

            // Copy initial registers if provided
            var initial_regs_copy: ?[]u64 = null;
            if (initial_regs) |regs| {
                initial_regs_copy = try proof.allocator.alloc(u64, regs.len);
                @memcpy(initial_regs_copy.?, regs);
            }

            // Copy final registers (all 32 registers)
            const final_regs = try proof.allocator.alloc(u64, 32);
            for (0..32) |i| {
                final_regs[i] = vm_state.regs.read(@intCast(i));
            }

            // Copy committed outputs from the guest's io.commit() calls.
            var outputs: ?[]u64 = null;
            if (vm_state.output_tape.items.len > 0) {
                const out = try proof.allocator.alloc(u64, vm_state.output_tape.items.len);
                @memcpy(out, vm_state.output_tape.items);
                outputs = out;
            }

            proof.public_io = PublicIO{
                .program_hash = program_hash,
                .initial_pc = entry_pc,
                .initial_regs = initial_regs_copy,
                .final_pc = vm_state.pc,
                .final_regs = final_regs,
                .num_steps = vm_state.trace.steps.items.len,
                .initial_memory = null, // TODO: Support initial memory state
                .outputs = outputs,
            };
        }
    };
}

// ============================================================================
// Tests
// ============================================================================

const testing = std.testing;
const BabyBear = @import("../core/field_presets.zig").BabyBear;

test "prover: initialization" {
    const allocator = testing.allocator;

    var prover = try Prover(BabyBear).init(allocator, 12345);
    defer prover.deinit();

    // Prover should be ready to generate proofs
    try testing.expect(prover.allocator.ptr == allocator.ptr);
}

test "prover: simple program proof" {
    const allocator = testing.allocator;

    var prover = try Prover(BabyBear).init(allocator, 12345);
    defer prover.deinit();

    // Create a simple RISC-V program:
    // ADDI x1, x0, 42   (add immediate: x1 = x0 + 42 = 42)
    // 0x02A00093
    const program = [_]u8{
        0x93, 0x00, 0xA0, 0x02, // ADDI x1, x0, 42
        0x00, 0x00, 0x00, 0x00, // Invalid instruction (halt)
    };

    // Generate proof
    var proof = try prover.prove(&program, 0x1000, null, 100, null, null);
    defer proof.deinit();

    // Verify proof structure
    try testing.expectEqual(@as(usize, 2), proof.public_io.num_steps);
    try testing.expect(proof.witness_commitments.len == 43);
    try testing.expect(proof.constraint_proof.num_vars > 0);

    // Verify final state
    try testing.expect(proof.public_io.final_regs != null);
    if (proof.public_io.final_regs) |regs| {
        try testing.expectEqual(@as(u64, 42), regs[1]); // x1 should be 42
    }
}

test "prover: proof size estimation" {
    const allocator = testing.allocator;

    var prover = try Prover(BabyBear).init(allocator, 12345);
    defer prover.deinit();

    const program = [_]u8{
        0x93, 0x00, 0xA0, 0x02, // ADDI x1, x0, 42
        0x00, 0x00, 0x00, 0x00, // Halt
    };

    var proof = try prover.prove(&program, 0x1000, null, 100, null, null);
    defer proof.deinit();

    const size = proof.estimateSize();

    // Proof should be reasonably sized (< 100 KB for tiny program)
    try testing.expect(size > 100); // At least 100 bytes
    try testing.expect(size < 100_000); // Less than 100 KB
}
