-- Groth16Verifier.ProofOfKnowledge
--
-- PROOF-OF-KNOWLEDGE
--
-- Proof-of-knowledge (PoK) is stronger than soundness.
--
-- Soundness says: if the verifier accepts, a witness *exists*.
-- Proof-of-knowledge says: there is a computable extractor E such that,
-- for any accepting proof π, E(π, x) *is* a valid witness.
--
-- Crucially, this is stated in terms of `verifyGroth16` (the Aiken
-- implementation) rather than `Groth16Valid` (the math spec). That is only
-- possible because the Correctness theorem bridges the two. Verifying the verifier
-- is what grounds the PoK claim at the level of the deployed contract:
--
--   verifyGroth16 = true
--   ↔ Groth16Valid          (Correctness — the verified verifier)
--   → ∃ w, R1CS x w         (AGM extractor axiom)
--
-- See: Firsov & Livshits, "The Ouroboros of ZK" (ePrint 2024/768).

import Groth16Verifier.Soundness

namespace Groth16Verifier.ProofOfKnowledge

open Groth16Verifier
open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec
open Groth16Verifier.Impl Groth16Verifier.Correctness Groth16Verifier.Soundness

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── Definition ────────────────────────────────────────────────────────────────

/-- A relation R satisfies proof-of-knowledge for `verifyGroth16` if there
    exists a computable extractor E such that for every accepting proof π and
    public inputs x, E(π, x) is a valid witness for R(x, ·).

    This is stated in terms of `verifyGroth16` (the Aiken implementation),
    not `Groth16Valid` (the mathematical spec). The Correctness theorem is what
    makes the two interchangeable — and therefore what makes this formulation
    meaningful at the implementation level. -/
def ProofOfKnowledge
    (R1CS : R1CSRelation Fr)
    (pd   : PairingData Fr G1 G2 GT)
    (vk   : VerifyingKey G1 G2) : Prop :=
  ∃ Extract : Proof G1 G2 → List Fr → List Fr,
    ∀ (π : Proof G1 G2) (x : List Fr),
      verifyGroth16 pd vk π x = true →
      R1CS x (Extract π x)

-- ── Theorem ───────────────────────────────────────────────────────────────────

/-- The Groth16 implementation satisfies proof-of-knowledge under the AGM.

    The extractor applies the AGM knowledge extractor axiom: given an accepting
    proof, it recovers the witness that the prover must have known.

    The key step is `verifyGroth16_correct`: because we have formally verified
    the Aiken verifier, we can convert an implementation-level acceptance into
    the mathematical predicate `Groth16Valid`, and then invoke the AGM extractor.
    Without the Correctness theorem this statement could only be made at the level
    of the abstract spec — not for the deployed contract. -/
theorem groth16_is_proof_of_knowledge
    (R1CS : R1CSRelation Fr)
    (pd   : PairingData Fr G1 G2 GT)
    (vk   : VerifyingKey G1 G2) :
    ProofOfKnowledge R1CS pd vk := by
  use fun π x =>
    if h : Groth16Valid pd vk π x
    then (agm_knowledge_extractor R1CS pd vk π x h).choose
    else []
  intro π x h_acc
  have h_valid : Groth16Valid pd vk π x :=
    (verifyGroth16_correct pd vk π x).mp h_acc
  simp only [dif_pos h_valid]
  exact (agm_knowledge_extractor R1CS pd vk π x h_valid).choose_spec

end Groth16Verifier.ProofOfKnowledge
