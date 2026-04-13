-- Groth16Verifier.Properties.ZeroKnowledge
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

import Groth16Verifier.Properties.Soundness

namespace Groth16Verifier.Properties.ZeroKnowledge

open Groth16Verifier
open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec Groth16Verifier.Impl
     Groth16Verifier.Properties.Correctness Groth16Verifier.Properties.Soundness
     Groth16Verifier.Properties.CompletenessProver

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
-- The honest prover's output is distributed identically to the simulator's.
-- "Perfect" ZK means the distributions are exactly equal (not just
-- computationally indistinguishable). Groth16 achieves perfect ZK.
--
-- Here we model it as equality of the concrete honest prover output and the
-- simulator output on valid instances, for any choice of prover randomness r, s.
--
-- In a full mechanisation this would be stated over a probability monad.

axiom groth16_perfect_zk
    (td      : Trapdoor)
    (R1CS    : R1CSRelation Fr)
    (crs     : CRS Fr)
    (qap     : QAPEval Fr)
    (g1      : G1) (g2 : G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_r1cs  : R1CS inputs witness) :
    -- The honest prover's output equals the simulator's output
    honestProver g1 g2 crs qap (inputs ++ witness) inputs.length r s
    = Sim td (mkVk g1 g2 crs qap inputs.length) inputs

-- ── Corollary: Simulated Proofs Verify ────────────────────────────────────────

/-- Simulated proofs (which don't use the witness) still verify.
    This follows from ZK + completeness:
    since sim(τ, x) = prove(x, w) and prove(x, w) verifies, sim verifies too. -/
theorem simulated_proof_verifies
    (td      : Trapdoor)
    (R1CS    : R1CSRelation Fr)
    (pd      : PairingData Fr G1 G2 GT)
    (crs     : CRS Fr)
    (qap     : QAPEval Fr)
    (g1      : G1) (g2 : G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 (mkVk g1 g2 crs qap inputs.length) inputs) :
    verifyGroth16 pd
      (mkVk g1 g2 crs qap inputs.length)
      (Sim td (mkVk g1 g2 crs qap inputs.length) inputs)
      inputs = true := by
  rw [← groth16_perfect_zk Trapdoor Sim td R1CS crs qap g1 g2 inputs witness r s h_r1cs]
  exact Completeness.verifyGroth16_complete pd R1CS crs qap g1 g2 inputs witness r s h_r1cs h_wf

-- ── Witness Indistinguishability ──────────────────────────────────────────────

/-- Proofs for the same statement with different witnesses are indistinguishable.
    Follows from: both equal the simulator's output (by ZK). -/
theorem witness_indistinguishable
    (td       : Trapdoor)
    (Sim'     : Trapdoor → VerifyingKey G1 G2 → List Fr → Proof G1 G2)
    (R1CS     : R1CSRelation Fr)
    (crs      : CRS Fr)
    (qap      : QAPEval Fr)
    (g1       : G1) (g2 : G2)
    (inputs   : List Fr)
    (witness₁ : List Fr)
    (witness₂ : List Fr)
    (r₁ s₁    : Fr)
    (r₂ s₂    : Fr)
    (h_r1cs₁  : R1CS inputs witness₁)
    (h_r1cs₂  : R1CS inputs witness₂) :
    honestProver g1 g2 crs qap (inputs ++ witness₁) inputs.length r₁ s₁
    = honestProver g1 g2 crs qap (inputs ++ witness₂) inputs.length r₂ s₂ := by
  rw [groth16_perfect_zk Trapdoor Sim' td R1CS crs qap g1 g2 inputs witness₁ r₁ s₁ h_r1cs₁,
      groth16_perfect_zk Trapdoor Sim' td R1CS crs qap g1 g2 inputs witness₂ r₂ s₂ h_r1cs₂]

end Groth16Verifier.Properties.ZeroKnowledge
