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

open Groth16Verifier.Algebra Groth16Verifier.Types
open scoped BigOperators

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── vk_x: the public-input commitment ────────────────────────────────────────
--
-- vk_x = IC[0] + x₁·IC[1] + x₂·IC[2] + ... + xₙ·IC[n]
--
-- This "commits" the public inputs into a single G1 point that can be
-- included in a pairing check.

def vkX (vk : VerifyingKey G1 G2) (inputs : List Fr) : G1 :=
  match vk.ic with
  | []          => 0
  | ic0 :: rest =>
    ic0 + (List.zipWith (· • ·) inputs rest).sum

-- ── Lemmas about vkX ─────────────────────────────────────────────────────────

@[simp]
lemma vkX_empty_ic (inputs : List Fr) :
    vkX (G2 := G2) { alpha := (0:G1), beta := (0:G2), gamma := 0,
                     delta := 0, ic := [] } inputs = 0 := by
  simp [vkX]

lemma vkX_nil_inputs (vk : VerifyingKey G1 G2) (ic0 : G1) (rest : List G1)
    (h : vk.ic = ic0 :: rest) :
    vkX vk ([] : List Fr) = ic0 := by
  simp [vkX, h, List.zipWith_nil_left]

lemma vkX_cons (vk : VerifyingKey G1 G2) (ic0 : G1) (rest : List G1)
    (x : Fr) (xs : List Fr) (h : vk.ic = ic0 :: rest) :
    vkX vk (x :: xs) =
      ic0 + x • (rest.head?.getD 0) + vkX { vk with ic := (0 :: rest.tail) } xs := by
  cases rest with
  | nil        => simp [vkX, h, smul_zero]
  | cons r0 rest' => simp [vkX, h]; abel

-- ── The Groth16 Verification Predicate ───────────────────────────────────────

/-- A proof is valid if it satisfies the Groth16 pairing equation -/
def Groth16Valid
    (pd     : PairingData Fr G1 G2 GT)
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) : Prop :=
  pd.pairing proof.A proof.B =
    pd.pairing vk.alpha vk.beta *
    pd.pairing (vkX vk inputs) vk.gamma *
    pd.pairing proof.C vk.delta

instance instDecidableGroth16Valid
    (pd     : PairingData Fr G1 G2 GT)
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
    (pd     : PairingData Fr G1 G2 GT)
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) : Prop :=
  pd.pairing (-proof.A) proof.B *
  pd.pairing vk.alpha   vk.beta *
  pd.pairing (vkX vk inputs) vk.gamma *
  pd.pairing proof.C    vk.delta = 1

/-- The two formulations are equivalent -/
theorem groth16Valid_iff_neg
    (pd     : PairingData Fr G1 G2 GT)
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
