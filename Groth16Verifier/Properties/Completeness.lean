-- Groth16Verifier.Properties.Completeness
--
-- COMPLETENESS THEOREM
--
-- If an honest prover has a valid witness for a satisfied R1CS instance,
-- their proof will always be accepted by the verifier.
--
-- This follows directly from:
--   1. The Correctness theorem (verifier = true ↔ equation holds)
--   2. The concrete proof in CompletenessProver that the honest prover's
--      output satisfies the pairing equation (modulo two named sorries)

import Groth16Verifier.Properties.CompletenessProver

namespace Groth16Verifier.Properties.Completeness

open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec Groth16Verifier.Impl
     Groth16Verifier.Properties.Correctness Groth16Verifier.Properties.CompletenessProver

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── Completeness Theorem ──────────────────────────────────────────────────────

/-- An honest prover with a valid witness is always accepted by the verifier. -/
theorem verifyGroth16_complete
    (pd      : PairingData Fr G1 G2 GT)
    (R1CS    : R1CSRelation Fr)
    (crs     : CRS Fr)
    (qap     : QAPEval Fr)
    (g1      : G1)
    (g2      : G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 (mkVk g1 g2 crs qap inputs.length) inputs) :
    verifyGroth16 pd
      (mkVk g1 g2 crs qap inputs.length)
      (honestProver g1 g2 crs qap (inputs ++ witness) inputs.length r s)
      inputs = true :=
  concrete_prover_correct g1 g2 pd crs R1CS qap inputs witness r s h_r1cs h_wf

-- ── No False Negatives ────────────────────────────────────────────────────────

/-- The verifier never rejects a correctly generated proof. -/
lemma verifyGroth16_no_false_negatives
    (pd      : PairingData Fr G1 G2 GT)
    (R1CS    : R1CSRelation Fr)
    (crs     : CRS Fr)
    (qap     : QAPEval Fr)
    (g1      : G1)
    (g2      : G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 (mkVk g1 g2 crs qap inputs.length) inputs) :
    ¬ (verifyGroth16 pd
        (mkVk g1 g2 crs qap inputs.length)
        (honestProver g1 g2 crs qap (inputs ++ witness) inputs.length r s)
        inputs = false) := by
  simp [verifyGroth16_complete pd R1CS crs qap g1 g2 inputs witness r s h_r1cs h_wf]

end Groth16Verifier.Properties.Completeness
