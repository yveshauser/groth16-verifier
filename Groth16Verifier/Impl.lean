-- Groth16Verifier.Impl
--
-- Lean transliteration of the Aiken `verify_groth16` function.
-- This is the implementation we are verifying — it mirrors the
-- groth16_verifier.ak contract as closely as possible so that
-- the Correctness theorem bridges the two artefacts.

import Groth16Verifier.Spec

namespace Groth16Verifier.Impl

open Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ── computeVkX ───────────────────────────────────────────────────────────────
-- Mirrors the Aiken `compute_vk_x` function.
-- Uses List.foldl over zipped (input, ic_point) pairs — matching the Aiken
-- implementation exactly.

def computeVkX (ic : List G1) (inputs : List Fr) : G1 :=
  match ic with
  | []          => 0
  | ic0 :: rest =>
    List.foldl
      (fun acc pair => acc + pair.1 • pair.2)
      ic0
      (inputs.zip rest)

-- ── verifyGroth16 ─────────────────────────────────────────────────────────────
-- Mirrors the Aiken `verify_groth16` function exactly.

def verifyGroth16
    (pd     : PairingData Fr G1 G2 GT)
    (vk     : VerifyingKey G1 G2)
    (proof  : Proof G1 G2)
    (inputs : List Fr) : Bool :=
  -- Guard: IC must have exactly (n_inputs + 1) elements
  if vk.ic.length ≠ inputs.length + 1 then false
  else
    -- Compute vk_x = IC[0] + Σ inputᵢ · ICᵢ₊₁
    let vk_x  := computeVkX vk.ic inputs
    -- Negate A for the additive form of the check
    let neg_a := -proof.A
    -- Compute product of all four Miller loops in GT
    let lhs :=
      pd.pairing neg_a     proof.B  *
      pd.pairing vk.alpha  vk.beta  *
      pd.pairing vk_x      vk.gamma *
      pd.pairing proof.C   vk.delta
    -- final_verify: check the product equals 1_GT
    decide (lhs = 1)

-- ── foldl / zipWith equivalence ──────────────────────────────────────────────
--
-- `List.foldl_zip_eq_sum_zipWith` is not in Mathlib under that name, so we
-- prove what we need directly.  The key identity is:
--
--   List.foldl (fun acc (s, P) => acc + s • P) init (xs.zip Ps)
--   = init + (List.zipWith (· • ·) xs Ps).sum

/-- Core foldl-over-zip identity.
    Proved by induction; the accumulator absorbs the initial value. -/
private lemma foldl_zip_smul_eq
    {α : Type*} [AddCommGroup α] [Module Fr α]
    (init : α) (xs : List Fr) (Ps : List α) :
    List.foldl (fun acc pair => acc + pair.1 • pair.2) init (xs.zip Ps)
    = init + (List.zipWith (· • ·) xs Ps).sum := by
  induction xs generalizing init Ps with
  | nil => simp
  | cons x xs ih =>
    cases Ps with
    | nil => simp
    | cons P Ps =>
      simp [List.zipWith]
      rw [ih (init + x • P)]
      -- init + x•P + Σ(zipWith) = init + (x•P + Σ(zipWith))
      abel

-- ── Equivalence: computeVkX = vkX ────────────────────────────────────────────
-- vkX uses List.zipWith + sum (clean for proofs)
-- computeVkX uses List.foldl  (mirrors the Aiken contract)

lemma computeVkX_eq_vkX
    (ic     : List G1)
    (inputs : List Fr) :
    computeVkX ic inputs = vkX (G2 := G2)
      { alpha := (0:G1), beta := (0:G2), gamma := 0, delta := 0, ic := ic }
      inputs := by
  simp [computeVkX, vkX]
  cases ic with
  | nil  => simp
  | cons ic0 rest =>
    simp
    rw [foldl_zip_smul_eq]

/-- The main form we use in the Correctness proof. -/
lemma computeVkX_eq_vkX_vk
    (vk     : VerifyingKey G1 G2)
    (inputs : List Fr) :
    computeVkX vk.ic inputs = vkX vk inputs := by
  simp only [vkX, computeVkX]
  cases h : vk.ic with
  | nil  => simp
  | cons ic0 rest =>
    simp only []
    rw [foldl_zip_smul_eq]

end Groth16Verifier.Impl
