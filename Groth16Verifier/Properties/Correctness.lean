-- Groth16Verifier.Correctness
--
-- CORRECTNESS THEOREM
--
-- The verifier is "correct": it returns `true` if and only if the
-- Groth16 pairing equation holds, assuming a well-formed verifying key.
--
--   verifyGroth16 pd vk proof inputs = true
--   ↔  Groth16Valid pd vk proof inputs    (given: wellFormed vk inputs)
--
-- This is a purely functional correctness property requiring no
-- cryptographic hardness assumptions — only the algebraic properties
-- of pairings (bilinearity, non-degeneracy).
--
-- This is the most important theorem in this library:
-- it bridges the Lean model and the Aiken implementation.

import Groth16Verifier.Impl
import Groth16Verifier.Spec

namespace Groth16Verifier.Correctness

open List Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec Groth16Verifier.Impl

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── foldl / zipWith equivalence ──────────────────────────────────────────────

/-- Generic foldl-over-zip identity: folding a binary operation over zipped lists
    equals the initial value plus the sum of zipWith applied to the lists.
    Proved by induction; the accumulator absorbs the initial value. -/
private lemma foldl_zip_eq
    {α β γ : Type*} [AddCommMonoid γ]
    (f : α → β → γ) (a₀ : γ) (xs : List α) (ys : List β) :
    foldl (fun acc pair => acc + f pair.1 pair.2) a₀ (zip xs ys)
    = a₀ + (zipWith f xs ys).sum := by
  induction xs generalizing a₀ ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp [zipWith]
      rw [ih (a₀ + f x y)]
      abel

-- ── Equivalence: computeVkX = vkX ────────────────────────────────────────────
-- vkX uses List.head + zipWith + sum (clean for proofs)
-- computeVkX uses List.head + List.foldl  (mirrors the Aiken contract)

/-- The main form we use in the Correctness proof. -/
lemma computeVkX_eq_vkX_vk
    (vk     : VerifyingKey G1 G2)
    (inputs : List Fr) :
    computeVkX vk.ic vk.h_ic0 inputs = vkX vk inputs := by
  simp [vkX, computeVkX, foldl_zip_eq]

-- ── Main Correctness Theorem ──────────────────────────────────────────────────

/-- The verifier returns `true` iff the Groth16 equation holds,
    assuming the IC list is well-formed (ic.length = inputs.length + 1).

    Proof:
    1. The length guard is disabled by `h_wf` → the `else` branch is taken.
    2. `computeVkX = vkX` (by `computeVkX_eq_vkX_vk`).
    3. `decide (lhs = 1) = true` ↔ `lhs = 1` (by `decide_eq_true_eq`).
    4. `lhs = 1` ↔ the pairing equation holds (by `groth16Valid_iff_neg`).
-/
theorem verifyGroth16_correct
    (pd     : PairingData Fr G1 G2 GT)
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr)
    (h_wf   : wellFormed Fr G1 G2 vk inputs) :
    verifyGroth16 pd vk proof inputs = true
    ↔ Groth16Valid pd vk proof inputs := by
  simp only [wellFormed] at h_wf
  simp only [verifyGroth16, h_wf, ne_eq, not_true, ite_false]
  -- Replace the foldl-based computeVkX with the sum-based vkX
  rw [computeVkX_eq_vkX_vk]
  -- `decide P = true ↔ P` for a decidable P
  rw [decide_eq_true_eq]
  -- The negated-form = 1 iff the standard Groth16 equation holds
  rw [groth16Valid_iff_neg pd vk proof inputs]
  simp [Groth16ValidNeg, mul_assoc]

-- ── Corollaries ───────────────────────────────────────────────────────────────

/-- The verifier returns `false` iff the equation does NOT hold -/
theorem verifyGroth16_false_iff
    (pd     : PairingData Fr G1 G2 GT)
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr)
    (h_wf   : wellFormed Fr G1 G2 vk inputs) :
    verifyGroth16 pd vk proof inputs = false
    ↔ ¬ Groth16Valid pd vk proof inputs := by
  rw [← Bool.not_eq_true]
  simp [verifyGroth16_correct pd vk proof inputs h_wf]

end Groth16Verifier.Correctness
