-- Groth16Verifier.Types
--
-- Core data types for Groth16 over BLS12-381.
-- Mirrors the Aiken contract's type definitions.

import Groth16Verifier.Algebra

namespace Groth16Verifier

variable (Fr : Type*) [Field Fr] [DecidableEq Fr]
variable (G1 : Type*) [AddCommGroup G1] [Module Fr G1]
variable (G2 : Type*) [AddCommGroup G2] [Module Fr G2]
variable (GT : Type*) [CommGroup GT]    [DecidableEq GT]

-- ── Verifying Key ─────────────────────────────────────────────────────────────
-- Generated once during the trusted setup ceremony.
-- Hardcoded into the validator — one contract per circuit.

structure VerifyingKey where
  /-- α ∈ G1: from the CRS -/
  alpha : G1
  /-- β ∈ G2: from the CRS -/
  beta  : G2
  /-- γ ∈ G2: from the CRS -/
  gamma : G2
  /-- δ ∈ G2: from the CRS -/
  delta : G2
  /-- IC ∈ G1^{n+1}: input commitment points.
      IC[0] is constant; IC[i] corresponds to public_inputs[i-1].
      Length = number_of_public_inputs + 1 -/
  ic    : List G1

-- ── Proof ─────────────────────────────────────────────────────────────────────
-- Three elliptic curve points: ~192 bytes compressed over BLS12-381.

structure Proof where
  /-- π_A ∈ G1 -/
  A : G1
  /-- π_B ∈ G2 -/
  B : G2
  /-- π_C ∈ G1 -/
  C : G1

-- ── R1CS Relation ─────────────────────────────────────────────────────────────
-- The NP relation the circuit encodes.
-- x = public inputs, w = private witness.

def R1CSRelation := List Fr → List Fr → Prop

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- A verifying key is well-formed for `n` public inputs iff ic has n+1 elements -/
def VerifyingKey.WellFormed (vk : VerifyingKey G1 G2) (n : ℕ) : Prop :=
  vk.ic.length = n + 1

/-- A proof redeemer is well-formed against a verifying key -/
def wellFormed (vk : VerifyingKey G1 G2) (inputs : List Fr) : Prop :=
  vk.ic.length = inputs.length + 1

end Groth16Verifier
