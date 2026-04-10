-- Groth16Verifier.Algebra
--
-- Abstract model of the BLS12-381 pairing groups.
-- Provides the algebraic axioms that the Plutus V3 builtins satisfy.
-- A concrete instance would instantiate these over the actual BLS12-381 curve.

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Group

namespace Groth16Verifier.Algebra

-- ── Type parameters ──────────────────────────────────────────────────────────

variable (Fr : Type*) [Field Fr] [DecidableEq Fr]
variable (G1 : Type*) [AddCommGroup G1] [Module Fr G1]
variable (G2 : Type*) [AddCommGroup G2] [Module Fr G2]
variable (GT : Type*) [CommGroup GT] [DecidableEq GT]

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
  /-- Non-degeneracy: pairing of non-zero points is non-trivial -/
  nondegen    : ∀ (P : G1) (Q : G2), P ≠ 0 → Q ≠ 0 → pairing P Q ≠ 1

-- ── Key derived lemmas ────────────────────────────────────────────────────────

variable {Fr G1 G2 GT} (pd : PairingData G1 G2 GT)

/-- Pairing of the zero element on the left gives 1 in GT.
    Proof: e(0, Q) = e(0+0, Q) = e(0,Q)·e(0,Q), so e(0,Q) = 1 by cancellation. -/
lemma pairing_zero_left (Q : G2) : pd.pairing 0 Q = 1 := by
  have h : pd.pairing 0 Q * pd.pairing 0 Q = pd.pairing 0 Q := by
    conv_rhs => rw [← add_zero (0 : G1)]
    rw [pd.bilin_left]
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- Pairing of the zero element on the right gives 1 in GT. -/
lemma pairing_zero_right (P : G1) : pd.pairing P 0 = 1 := by
  have h : pd.pairing P 0 * pd.pairing P 0 = pd.pairing P 0 := by
    conv_rhs => rw [← add_zero (0 : G2)]
    rw [pd.bilin_right]
  exact mul_left_cancel (h.trans (mul_one _).symm)

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
  rw [pairing_neg_left pd A B]
  constructor
  · intro h
    have h1 : pd.pairing A B *
              ((pd.pairing A B)⁻¹ * pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ) =
              pd.pairing α β * pd.pairing vk_x γ * pd.pairing C δ := by group
    rw [h, mul_one] at h1
    exact h1
  · intro h
    rw [h]
    group

end Groth16Verifier.Algebra
