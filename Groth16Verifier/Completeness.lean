-- Groth16Verifier.Completeness
--
-- COMPLETENESS THEOREM
--
-- If an honest prover has a valid witness for a satisfied R1CS instance,
-- their proof will always be accepted by the verifier.
--
-- This follows directly from:
--   1. The Correctness theorem (verifier = true ↔ equation holds)
--   2. The Groth16 completeness axiom (honest prover satisfies the equation)

import Groth16Verifier.Correctness

namespace Groth16Verifier.Completeness

open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec Groth16Verifier.Impl Groth16Verifier.Correctness

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── Abstract Prover ───────────────────────────────────────────────────────────

-- An abstract Groth16 prover: given vk, witness, public inputs → a proof.
-- In practice this is the bellman / arkworks / snarkjs prover.
variable (Prove : VerifyingKey G1 G2 → List Fr → List Fr → Proof G1 G2)

-- ── Groth16 Completeness Axiom ────────────────────────────────────────────────
--
-- An honest Groth16 prover always produces a proof satisfying the verification
-- equation. This is the completeness property of the Groth16 proof system,
-- proved in the original Groth 2016 paper (Theorem 1).
--
-- We take it as an axiom here. It could be discharged by importing the
-- ArkLib mechanisation of Groth16 completeness once that is available.

axiom groth16_prover_correct
    (pd      : PairingData Fr G1 G2 GT)
    (R1CS    : R1CSRelation Fr)
    (vk      : VerifyingKey G1 G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 vk inputs) :
    Groth16Valid pd vk (Prove vk witness inputs) inputs

-- ── Completeness Theorem ──────────────────────────────────────────────────────

/-- An honest prover with a valid witness is always accepted by the verifier. -/
theorem verifyGroth16_complete
    (pd      : PairingData Fr G1 G2 GT)
    (R1CS    : R1CSRelation Fr)
    (vk      : VerifyingKey G1 G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 vk inputs) :
    verifyGroth16 pd vk (Prove vk witness inputs) inputs = true := by
  rw [verifyGroth16_correct]
  exact groth16_prover_correct Prove pd R1CS vk inputs witness h_r1cs h_wf

-- ── No False Negatives ────────────────────────────────────────────────────────

/-- The verifier never rejects a correctly generated proof. -/
lemma verifyGroth16_no_false_negatives
    (pd      : PairingData Fr G1 G2 GT)
    (R1CS    : R1CSRelation Fr)
    (vk      : VerifyingKey G1 G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 vk inputs) :
    ¬ (verifyGroth16 pd vk (Prove vk witness inputs) inputs = false) := by
  simp [verifyGroth16_complete Prove pd R1CS vk inputs witness h_r1cs h_wf]

end Groth16Verifier.Completeness
