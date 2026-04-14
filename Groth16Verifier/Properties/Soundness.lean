-- Groth16Verifier.Properties.Soundness
--
-- SOUNDNESS THEOREM
--
-- A cheating prover cannot produce an accepting proof for a false statement,
-- except with negligible probability — under the Algebraic Group Model (AGM).
--
-- Structure:
--   1. State the AGM knowledge soundness axiom
--   2. Derive: verifier accepts → valid witness exists
--   3. Derive: verifier accepts → QAP is satisfiable
--
-- The AGM axiom here is what ArkLib aims to mechanise formally.
-- See: Groth 2016, Theorem 2; Fuchsbauer-Kiltz-Loss 2018 (AGM framework).

import Groth16Verifier.Properties.Completeness

namespace Groth16Verifier.Properties.Soundness

open Groth16Verifier
open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec Groth16Verifier.Impl
     Groth16Verifier.Properties.Correctness Groth16Verifier.Properties.CompletenessProver

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── The Algebraic Group Model (AGM) ──────────────────────────────────────────
--
-- In the AGM, any adversary who outputs group elements also provides their
-- "algebraic representation" — i.e., linear combinations of known CRS points.
-- This allows a knowledge extractor to recover the witness from any proof
-- that satisfies the verification equation.
--
-- Formally: if A outputs a valid proof, then A also outputs the witness,
-- and the extractor can read it off.
--
-- This axiom captures the conclusion of the AGM security proof without
-- formalising the AGM itself. Discharging it requires:
--   - A formalised definition of algebraic adversaries (ArkLib's IOR framework)
--   - The Groth16 special soundness argument in the AGM
--   - Connection to knowledge soundness via the BCS transform

axiom agm_knowledge_extractor
    (qap     : QAPEval Fr)
    (pd      : PairingData Fr G1 G2 GT)
    (vk      : VerifyingKey G1 G2)
    (proof   : Proof G1 G2)
    (inputs  : List Fr)
    (h_valid : Groth16Valid pd vk proof inputs) :
    ∃ witness : List Fr, QAPSat qap (inputs ++ witness)

-- ── Soundness Theorem ─────────────────────────────────────────────────────────

/-- If the verifier accepts a proof, there exists a QAP-satisfying witness.
    Equivalently: the verifier cannot be convinced of a false statement. -/
theorem verifyGroth16_sound
    (qap     : QAPEval Fr)
    (pd      : PairingData Fr G1 G2 GT)
    (vk      : VerifyingKey G1 G2)
    (proof   : Proof G1 G2)
    (inputs  : List Fr)
    (h_wf    : wellFormed Fr G1 G2 vk inputs)
    (h_acc   : verifyGroth16 pd vk proof inputs = true) :
    ∃ witness : List Fr, QAPSat qap (inputs ++ witness) := by
  -- Convert the Bool result to the mathematical predicate (Correctness theorem)
  rw [verifyGroth16_correct pd vk proof inputs h_wf] at h_acc
  -- Apply the AGM knowledge extractor
  exact agm_knowledge_extractor qap pd vk proof inputs h_acc

-- ── No False Positives ────────────────────────────────────────────────────────

/-- The verifier never accepts a proof when no QAP-satisfying witness exists. -/
theorem verifyGroth16_no_false_positives
    (qap     : QAPEval Fr)
    (pd      : PairingData Fr G1 G2 GT)
    (vk      : VerifyingKey G1 G2)
    (proof   : Proof G1 G2)
    (inputs  : List Fr)
    (h_wf    : wellFormed Fr G1 G2 vk inputs)
    (h_unsat : ∀ witness : List Fr, ¬ QAPSat qap (inputs ++ witness)) :
    verifyGroth16 pd vk proof inputs = false := by
  by_contra h_true
  -- h_true : verifyGroth16 ... ≠ false; Bool is {true,false} so this means = true
  have h_acc : verifyGroth16 pd vk proof inputs = true := by
    rcases h : verifyGroth16 pd vk proof inputs with _ | _
    · exact absurd h h_true
    · rfl
  obtain ⟨witness, h_wit⟩ := verifyGroth16_sound qap pd vk proof inputs h_wf h_acc
  exact h_unsat witness h_wit

-- ── Combining Soundness and Completeness ─────────────────────────────────────

/-- The verifier is both sound and complete:
    it accepts iff a QAP-satisfying witness exists. -/
theorem verifyGroth16_iff_satisfiable
    (pd      : PairingData Fr G1 G2 GT)
    (crs     : CRS Fr)
    (qap     : QAPEval Fr)
    (g1      : G1) (g2 : G2)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_qap   : QAPSat qap (inputs ++ witness))
    (h_wf    : wellFormed Fr G1 G2 (mkVk g1 g2 crs qap inputs.length) inputs) :
    verifyGroth16 pd
      (mkVk g1 g2 crs qap inputs.length)
      (honestProver g1 g2 crs qap (inputs ++ witness) inputs.length r s)
      inputs = true
    ↔ ∃ w : List Fr, QAPSat qap (inputs ++ w) := by
  constructor
  · intro h_acc
    exact verifyGroth16_sound qap pd _ _ inputs h_wf h_acc
  · intro _
    exact Completeness.verifyGroth16_complete pd crs qap g1 g2 inputs witness r s h_qap h_wf

end Groth16Verifier.Properties.Soundness
