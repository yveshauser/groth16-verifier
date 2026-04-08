-- Groth16Verifier.Impl
--
-- Lean transliteration of the Aiken `verify_groth16` function.
-- This is the implementation we are verifying — it mirrors the
-- groth16_verifier.ak contract as closely as possible

import Groth16Verifier.Algebra
import Groth16Verifier.Types

namespace Groth16Verifier.Impl

open Groth16Verifier.Algebra Groth16Verifier.Types

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]
variable (pd : PairingData Fr G1 G2 GT)

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

end Groth16Verifier.Impl
