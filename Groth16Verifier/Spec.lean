-- Groth16Verifier.Spec
--
-- The ground-truth mathematical specification of Groth16 verification.
-- This is what the verifier *should* compute — independent of any implementation.
--
-- The Groth16 verification equation (Groth 2016, §3.2):
--
--   e(A, B) = e(α, β) · e(vk_x, γ) · e(C, δ)
--
-- where vk_x = IC[0] + Σᵢ xᵢ · IC[i+1]  (linear combination over G1)

import Groth16Verifier.Types
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Abel

namespace Groth16Verifier.Spec

open List Groth16Verifier.Algebra Groth16Verifier.Types
open scoped BigOperators

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

variable (pd : PairingData G1 G2 GT)

-- ── vk_x: the public-input commitment ────────────────────────────────────────
--
-- vk_x = IC[0] + x₁·IC[1] + x₂·IC[2] + ... + xₙ·IC[n]
--
-- This "commits" the public inputs into a single G1 point that can be
-- included in a pairing check.

def vkX (vk : VerifyingKey G1 G2) (inputs : List Fr) : G1 :=
  let ic0  := head vk.ic vk.h_ic0
  let rest := tail vk.ic
  ic0 + (zipWith (· • ·) inputs rest).sum

-- ── The Groth16 Verification Predicate ───────────────────────────────────────

/-- A proof is valid if it satisfies the Groth16 pairing equation -/
def Groth16Valid
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) : Prop :=
  pd.pairing proof.A proof.B =
    pd.pairing vk.alpha vk.beta *
    pd.pairing (vkX vk inputs) vk.gamma *
    pd.pairing proof.C vk.delta

instance instDecidableGroth16Valid
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) :
    Decidable (Groth16Valid pd vk proof inputs) :=
  inferInstanceAs (Decidable (pd.pairing proof.A proof.B =
    pd.pairing vk.alpha vk.beta *
    pd.pairing (vkX vk inputs) vk.gamma *
    pd.pairing proof.C vk.delta))

-- ── Reformulation: the negated-A form ────────────────────────────────────────
-- This is how the Aiken contract checks it:
--   e(-A,B) · e(α,β) · e(vk_x,γ) · e(C,δ) = 1

def Groth16ValidNeg
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) : Prop :=
  pd.pairing (-proof.A) proof.B *
  pd.pairing vk.alpha   vk.beta *
  pd.pairing (vkX vk inputs) vk.gamma *
  pd.pairing proof.C    vk.delta = 1

/-- The two formulations are equivalent -/
theorem groth16Valid_iff_neg
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) :
    Groth16Valid pd vk proof inputs ↔ Groth16ValidNeg pd vk proof inputs := by
  simp only [Groth16Valid, Groth16ValidNeg]
  rw [pairing_neg_left pd]
  -- Goal: e(A,B) = rhs ↔ e(A,B)⁻¹ · rhs = 1
  -- where rhs = e(α,β) · e(vkx,γ) · e(C,δ)
  constructor
  · intro h
    rw [h]; group
  · intro h
    -- e(A,B)⁻¹ · rhs = 1 → rhs = e(A,B)
    have := mul_eq_one_iff_eq_inv.mp
      (show (pd.pairing proof.A proof.B)⁻¹ *
            (pd.pairing vk.alpha vk.beta *
             pd.pairing (vkX vk inputs) vk.gamma *
             pd.pairing proof.C vk.delta) = 1 by
        calc (pd.pairing proof.A proof.B)⁻¹ *
               (pd.pairing vk.alpha vk.beta *
                pd.pairing (vkX vk inputs) vk.gamma *
                pd.pairing proof.C vk.delta)
            = (pd.pairing proof.A proof.B)⁻¹ *
                pd.pairing vk.alpha vk.beta *
                pd.pairing (vkX vk inputs) vk.gamma *
                pd.pairing proof.C vk.delta := by group
          _ = 1 := h)
    exact inv_inj.mp this

end Groth16Verifier.Spec
