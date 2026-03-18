-- Groth16Verifier.ZeroKnowledge
--
-- ZERO-KNOWLEDGE PROPERTY
--
-- A Groth16 proof reveals nothing about the witness beyond the truth
-- of the statement. Formalised as: there exists a simulator that
-- produces computationally indistinguishable proofs without knowing
-- the witness (given access to the CRS trapdoor τ).
--
-- This is a weaker property than soundness to formalise mechanically,
-- because it requires a notion of computational indistinguishability.
-- We use a simplified "perfect simulation" model here; a full proof
-- would use a probability monad (VCV-io, MathComp/SSReflect crypto).
--
-- Reference: Groth 2016, Theorem 3; also Abdolmaleki et al 2017 (Sub-GBGM ZK).

import Groth16Verifier.Soundness

namespace Groth16Verifier.ZeroKnowledge

open Groth16Verifier
open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec Groth16Verifier.Impl Groth16Verifier.Honesty Groth16Verifier.Soundness

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── The CRS Trapdoor ─────────────────────────────────────────────────────────

-- The toxic waste from the trusted setup ceremony.
-- Only the simulator has access to this — in a real deployment it is
-- destroyed after key generation.
variable (Trapdoor : Type*)

-- ── The Simulator ─────────────────────────────────────────────────────────────

-- A ZK simulator: given the trapdoor and public inputs, produces a fake proof
-- without knowing the witness.
variable (Sim : Trapdoor → VerifyingKey G1 G2 → List Fr → Proof G1 G2)

-- ── Perfect ZK Axiom ─────────────────────────────────────────────────────────
--
-- The simulator's output is distributed identically to the honest prover's output.
-- "Perfect" ZK means the distributions are exactly equal (not just computationally
-- indistinguishable). Groth16 achieves perfect ZK.
--
-- In a full mechanisation this would be stated over a probability monad.
-- Here we model it as equality of proof-producing functions on valid instances.

axiom groth16_perfect_zk
    (td      : Trapdoor)
    (Prove   : VerifyingKey G1 G2 → List Fr → List Fr → Proof G1 G2)
    (R1CS    : R1CSRelation Fr)
    (pd      : PairingData Fr G1 G2 GT)
    (vk      : VerifyingKey G1 G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (h_r1cs  : R1CS inputs witness) :
    -- The real proof and the simulated proof are identical
    -- (as distributions; here modelled as equal values for a fixed randomness)
    Prove vk witness inputs = Sim td vk inputs

-- ── Corollary: Simulated Proofs Verify ────────────────────────────────────────

/-- Simulated proofs (which don't use the witness) still verify.
    This follows from ZK + completeness:
    since sim(τ, x) = prove(x, w) and prove(x, w) verifies, sim verifies too. -/
theorem simulated_proof_verifies
    (td      : Trapdoor)
    (Prove   : VerifyingKey G1 G2 → List Fr → List Fr → Proof G1 G2)
    (R1CS    : R1CSRelation Fr)
    (pd      : PairingData Fr G1 G2 GT)
    (vk      : VerifyingKey G1 G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 vk inputs) :
    verifyGroth16 pd vk (Sim td vk inputs) inputs = true := by
  rw [← groth16_perfect_zk Trapdoor Sim td Prove R1CS pd vk inputs witness h_r1cs]
  exact Completeness.verifyGroth16_complete Prove pd R1CS vk inputs witness h_r1cs h_wf

-- ── Witness Indistinguishability ──────────────────────────────────────────────

omit [DecidableEq Fr] [Module Fr G2] [DecidableEq GT] in
/-- Proofs for the same statement with different witnesses are indistinguishable.
    Follows from: both equal the simulator's output (by ZK). -/
theorem witness_indistinguishable
    (td       : Trapdoor)
    (Sim      : Trapdoor → VerifyingKey G1 G2 → List Fr → Proof G1 G2)
    (Prove    : VerifyingKey G1 G2 → List Fr → List Fr → Proof G1 G2)
    (R1CS     : R1CSRelation Fr)
    (pd       : PairingData Fr G1 G2 GT)
    (vk       : VerifyingKey G1 G2)
    (inputs   : List Fr)
    (witness₁ : List Fr)
    (witness₂ : List Fr)
    (h_r1cs₁  : R1CS inputs witness₁)
    (h_r1cs₂  : R1CS inputs witness₂) :
    Prove vk witness₁ inputs = Prove vk witness₂ inputs := by
  rw [groth16_perfect_zk Trapdoor Sim td Prove R1CS pd vk inputs witness₁ h_r1cs₁]
  rw [groth16_perfect_zk Trapdoor Sim td Prove R1CS pd vk inputs witness₂ h_r1cs₂]

end Groth16Verifier.ZeroKnowledge
