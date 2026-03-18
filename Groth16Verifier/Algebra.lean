-- Groth16Verifier.Algebra
--
-- Abstract model of the BLS12-381 pairing groups.
-- Provides the algebraic axioms that the Plutus V3 builtins satisfy.
-- A concrete instance would instantiate these over the actual BLS12-381 curve.

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

namespace Groth16Verifier.Algebra

-- ── Type parameters ──────────────────────────────────────────────────────────

variable (Fr : Type*) [Field Fr] [DecidableEq Fr]
variable (G1 : Type*) [AddCommGroup G1] [Module Fr G1]
variable (G2 : Type*) [AddCommGroup G2] [Module Fr G2]
variable (GT : Type*) [CommGroup GT]    [DecidableEq GT]

-- ── The pairing ───────────────────────────────────────────────────────────────

structure PairingData where
  /-- The bilinear map -/
  pairing     : G1 → G2 → GT
  /-- Bilinearity in the first argument -/
  bilin_left  : ∀ (P Q : G1) (R : G2),
                  pairing (P + Q) R = pairing P R * pairing Q R
  /-- Bilinearity in the second argument -/
  bilin_right : ∀ (P : G1) (Q R : G2),
                  pairing P (Q + R) = pairing P Q * pairing P R
  /-- Compatibility with scalar multiplication on the left -/
  scalar_left : ∀ (s : Fr) (P : G1) (Q : G2) (n : ℕ),
                  (s : ℤ) = n →
                  pairing (s • P) Q = pairing P Q ^ n
  /-- Non-degeneracy: pairing of non-zero points is non-trivial -/
  nondegen    : ∀ (P : G1) (Q : G2), P ≠ 0 → Q ≠ 0 → pairing P Q ≠ 1

-- ── Key derived lemmas ────────────────────────────────────────────────────────

variable {Fr G1 G2 GT} (pd : PairingData Fr G1 G2 GT)

/-- Pairing of the zero element on the left gives 1 in GT.
    Proof: e(0, Q) = e(0+0, Q) = e(0,Q)·e(0,Q), so e(0,Q) = 1 by cancellation. -/
lemma pairing_zero_left (Q : G2) : pd.pairing 0 Q = 1 := by
  have h : pd.pairing 0 Q * pd.pairing 0 Q = pd.pairing 0 Q := by
    conv_lhs => rw [← add_zero (0 : G1)]
    rw [pd.bilin_left]
  -- In a group, x * x = x implies x = 1: cancel x on the right
  nth_rewrite 2 [← mul_one (pd.pairing 0 Q)] at h
  exact mul_left_cancel₀ (by
    intro heq
    simp [heq] at h) h

/-- Pairing of the zero element on the right gives 1 in GT. -/
lemma pairing_zero_right (P : G1) : pd.pairing P 0 = 1 := by
  have h : pd.pairing P 0 * pd.pairing P 0 = pd.pairing P 0 := by
    conv_lhs => rw [← add_zero (0 : G2)]
    rw [pd.bilin_right]
  nth_rewrite 2 [← mul_one (pd.pairing P 0)] at h
  exact mul_left_cancel₀ (by
    intro heq
    simp [heq] at h) h

/-- e(-P, Q) = e(P, Q)⁻¹.
    Proof: e(P,Q) · e(-P,Q) = e(P + (-P), Q) = e(0,Q) = 1. -/
lemma pairing_neg_left (P : G1) (Q : G2) :
    pd.pairing (-P) Q = (pd.pairing P Q)⁻¹ := by
  -- From bilinearity: e(P,Q) · e(-P,Q) = e(P + (-P), Q) = e(0,Q) = 1
  have h : pd.pairing P Q * pd.pairing (-P) Q = 1 := by
    rw [← pd.bilin_left P (-P) Q]
    simp [pairing_zero_left pd Q]
  -- From a · b = 1 we get b = a⁻¹
  exact eq_inv_of_mul_eq_one_right h

/-- Sum-of-pairings bilinearity: e distributes over a list sum in G1. -/
lemma pairing_sum_left (Ps : List G1) (Q : G2) :
    pd.pairing Ps.sum Q = (Ps.map (pd.pairing · Q)).prod := by
  induction Ps with
  | nil        => simp [pairing_zero_left pd Q]
  | cons P Ps ih =>
    simp [List.sum_cons, List.prod_cons, pd.bilin_left, ih]

-- ── The key multi-pairing identity ───────────────────────────────────────────
--
-- e(-A,B) · e(α,β) · e(vk_x,γ) · e(C,δ) = 1
-- ↔  e(A,B) = e(α,β) · e(vk_x,γ) · e(C,δ)
--
-- This is the algebraic core of the Groth16 verification equation.

lemma multipairing_eq_one_iff
    (A vk_x C α : G1) (B β γ δ : G2) :
    pd.pairing (-A) B * pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ = 1
    ↔
    pd.pairing A B = pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ := by
  -- Rewrite e(-A,B) = e(A,B)⁻¹
  rw [pairing_neg_left pd A B]
  -- Rename for readability
  set a := pd.pairing A B
  set r := pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ
  -- a⁻¹ · r = 1 ↔ a = r
  constructor
  · intro h
    -- a⁻¹ · r = 1 → r = a  (multiply both sides by a)
    have h' : (pd.pairing A B)⁻¹ *
              (pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ) = 1 := by
      calc (pd.pairing A B)⁻¹ *
             (pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ)
          = (pd.pairing A B)⁻¹ * pd.pairing α β *
              pd.pairing vk_x γ * pd.pairing C δ := by group
        _ = 1 := h
    exact (inv_mul_eq_one.mp h').symm
  · intro h
    rw [h]
    group

end Groth16Verifier.Algebra
