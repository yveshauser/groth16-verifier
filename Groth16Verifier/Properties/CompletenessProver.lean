-- Groth16Verifier.Properties.CompletenessProver
--
-- A concrete implementation of the honest Groth16 prover that reduces the
-- groth16_prover_correct axiom to two named gaps:
--
--   · sorry₁ (r1cs_implies_qap_sat):  R1CS satisfaction implies the QAP
--             divisibility condition at τ.  Requires polynomial evaluation
--             machinery (Mathlib's Polynomial library + Schwartz–Zippel).
--
--   · sorry₂ (honest_prover_pairing_eq): the pairing equation holds after
--             expanding the honest prover's output.  Requires a
--             pairing_smul_compat identity and GT algebra.
--
-- The four steps follow Groth 2016, §3 closely.

import Groth16Verifier.Properties.Correctness

namespace Groth16Verifier.Properties.CompletenessProver

open List Groth16Verifier.Algebra Groth16Verifier.Types Groth16Verifier.Spec
     Groth16Verifier.Impl Groth16Verifier.Properties.Correctness

variable {Fr : Type*} [Field Fr] [DecidableEq Fr]
variable {G1 : Type*} [AddCommGroup G1] [Module Fr G1]
variable {G2 : Type*} [AddCommGroup G2] [Module Fr G2]
variable {GT : Type*} [CommGroup GT]    [DecidableEq GT]

-- ═══════════════════════════════════════════════════════════════════════════
-- STEP 1: COMMON REFERENCE STRING
-- ═══════════════════════════════════════════════════════════════════════════
--
-- The CRS is produced by the trusted setup ceremony.
-- It holds secret scalars in Fr whose integer lifts are never revealed.
-- The prover and verifier receive only elliptic-curve encodings of these
-- scalars (the structured reference string).

structure CRS (Fr : Type*) [Field Fr] where
  alpha : Fr  -- blinding factor for proof element A
  beta  : Fr  -- blinding factor for proof element B
  gamma : Fr  -- denominator for public-input IC points
  delta : Fr  -- denominator for private-input / ZK randomness
  tau   : Fr  -- QAP evaluation point ("toxic waste" — discarded after setup)
  h_gamma : gamma ≠ 0
  h_delta : delta ≠ 0

-- Generators: fixed non-zero base points.
-- In BLS12-381 these are the standard generators P₁ ∈ G1, P₂ ∈ G2.
variable (g1 : G1) (g2 : G2)

-- ═══════════════════════════════════════════════════════════════════════════
-- STEP 2: QUADRATIC ARITHMETIC PROGRAM
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Every R1CS circuit can be encoded as a QAP (Gennaro et al. 2012).
-- We represent the QAP by its constraint polynomials {uᵢ, vᵢ, wᵢ} already
-- *evaluated at τ* — not as symbolic polynomials — since the prover only
-- needs these evaluations.
--
-- For a circuit with m+1 wires (wire 0 = constant "1", wires 1..ℓ = public
-- inputs, wires ℓ+1..m = private witness):
--
--   uᵢ(τ), vᵢ(τ), wᵢ(τ)   for i = 0 .. m   (one scalar per wire)
--   t(τ)                     target polynomial at τ
--   h(τ)                     quotient: p(τ) / t(τ)  where p = Σ aᵢ(uᵢ·vᵢ − wᵢ)
--
-- QAP satisfiability at τ (Groth 2016, §3.1):
--   (Σ aᵢ uᵢ(τ)) · (Σ aᵢ vᵢ(τ)) = Σ aᵢ wᵢ(τ) + h(τ)·t(τ)
-- This holds iff the assignment a satisfies the R1CS constraints.

structure QAPEval (Fr : Type*) [Field Fr] where
  -- Evaluated polynomials, one entry per wire (length = m+1).
  u  : List Fr   -- uᵢ(τ)
  v  : List Fr   -- vᵢ(τ)
  w  : List Fr   -- wᵢ(τ)
  t  : Fr        -- t(τ)
  h  : Fr        -- h(τ)

-- Weighted inner product: Σᵢ aᵢ · bᵢ  (lists are truncated to the shorter)
private def wsum (a b : List Fr) : Fr := (zipWith (· * ·) a b).sum

-- QAP satisfiability condition for a full assignment a = inputs ++ witness
def QAPSat (qap : QAPEval Fr) (a : List Fr) : Prop :=
  wsum a qap.u * wsum a qap.v = wsum a qap.w + qap.h * qap.t

-- KEY GAP (sorry₁):
--   R1CS satisfaction implies QAP satisfiability at τ.
--
--   This is the Groth–Gennaro QAP reduction: if a satisfies all R1CS
--   constraints, then the polynomial p(X) = Σ aᵢ(uᵢ(X)·vᵢ(X) − wᵢ(X))
--   is divisible by t(X), so evaluating at τ gives QAPSat.
--
--   Proof sketch:
--     (a) R1CS → t | p  (polynomial divisibility from constraint satisfaction)
--     (b) t | p  →  p(τ) = h(τ)·t(τ) for the specific h chosen by the prover
--
--   Blocked on: Mathlib Polynomial.eval, the QAP encoding of R1CS, and
--               the Schwartz–Zippel argument that τ is not a spurious root.
lemma r1cs_implies_qap_sat
    (R1CS    : R1CSRelation Fr)
    (qap     : QAPEval Fr)
    (inputs  : List Fr)
    (witness : List Fr)
    (h_r1cs  : R1CS inputs witness) :
    QAPSat qap (inputs ++ witness) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- STEP 3: VERIFYING KEY AND HONEST PROVER OUTPUT
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Verifying key (public — embedded in the on-chain validator):
--
--   vk.alpha  = α · g1
--   vk.beta   = β · g2
--   vk.gamma  = γ · g2
--   vk.delta  = δ · g2
--   vk.ic[i]  = (β·uᵢ(τ) + α·vᵢ(τ) + wᵢ(τ)) / γ · g1   for i = 0..ℓ
--
-- The prover also receives private proving-key elements (not stored here):
--   pk.L[i]   = (β·uᵢ(τ) + α·vᵢ(τ) + wᵢ(τ)) / δ · g1   for private i

-- Scalar coefficient for IC[i]
private def icScalar (crs : CRS Fr) (qap : QAPEval Fr) (i : ℕ) : Fr :=
  (crs.beta  * qap.u.getD i 0 +
   crs.alpha * qap.v.getD i 0 +
               qap.w.getD i 0) / crs.gamma

-- IC point list: ℓ+1 elements, one per public wire
private def mkIC (crs : CRS Fr) (qap : QAPEval Fr) (n_pub : ℕ) : List G1 :=
  (range (n_pub + 1)).map (fun i => icScalar crs qap i • g1)

omit [DecidableEq Fr] in
private lemma mkIC_ne_nil (crs : CRS Fr) (qap : QAPEval Fr) (n_pub : ℕ) :
    mkIC g1 crs qap n_pub ≠ [] := by
  simp [mkIC, List.map_eq_nil_iff, List.range_eq_nil]

-- Build the verifying key from the CRS and QAP
def mkVk (crs : CRS Fr) (qap : QAPEval Fr) (n_pub : ℕ) : VerifyingKey G1 G2 where
  alpha := crs.alpha • g1
  beta  := crs.beta  • g2
  gamma := crs.gamma • g2
  delta := crs.delta • g2
  ic    := mkIC g1 crs qap n_pub
  h_ic0 := mkIC_ne_nil g1 crs qap n_pub

-- Honest prover output (Groth 2016, §3.2).
-- r, s ∈ Fr are fresh random scalars (give zero-knowledge; completeness holds for any r, s).
--
--   A = (α + Σ aᵢ uᵢ(τ) + r·δ) · g1
--   B = (β + Σ aᵢ vᵢ(τ) + s·δ) · g2
--   C = ((Σ_{priv} aᵢ (β·uᵢ + α·vᵢ + wᵢ)(τ) + h(τ)·t(τ)) / δ
--         + s·A_val + r·B_val − r·s·δ) · g1
--
-- where A_val = α + Σ aᵢ uᵢ(τ) + r·δ  (the scalar used for A).

def honestProver
    (crs   : CRS Fr)
    (qap   : QAPEval Fr)
    (all   : List Fr)   -- inputs ++ witness  (full assignment)
    (n_pub : ℕ)         -- = inputs.length
    (r s   : Fr) :
    Proof G1 G2 :=
  let a_val := crs.alpha + wsum all qap.u + r * crs.delta
  let b_val := crs.beta  + wsum all qap.v + s * crs.delta
  -- Private-wire numerator: Σ_{priv} aᵢ (β·uᵢ + α·vᵢ + wᵢ)(τ)
  let priv      := all.drop n_pub
  let priv_ic_u := qap.u.drop n_pub |>.map (crs.beta  * ·)
  let priv_ic_v := qap.v.drop n_pub |>.map (crs.alpha * ·)
  let priv_ic_w := qap.w.drop n_pub
  let priv_sum  := wsum priv (zipWith (· + ·) (zipWith (· + ·) priv_ic_u priv_ic_v) priv_ic_w)
  let c_val := (priv_sum + qap.h * qap.t) / crs.delta
               + s * a_val + r * b_val - r * s * crs.delta
  { A := a_val • g1
    B := b_val • g2
    C := c_val • g1 }

-- ═══════════════════════════════════════════════════════════════════════════
-- STEP 4: ALGEBRAIC PROOF OF THE PAIRING EQUATION
-- ═══════════════════════════════════════════════════════════════════════════
--
-- After substituting the honest prover's A, B, C and the VK, the verification
-- equation e(A,B) = e(α,β)·e(vk_x,γ)·e(C,δ) reduces — via bilinearity — to
-- an algebraic identity in Fr that holds by QAPSat.
--
-- The reduction uses `pairing_smul_compat` from Algebra.lean:
--   e(a·P, b·Q) = e((a·b)·P, Q)
-- proved there via scalar_compat + smul_smul.

-- KEY GAP (sorry₂):
--   After unfolding honestProver and mkVk and applying pairing_smul_compat,
--   the goal becomes:
--
--     (a_val · b_val) = (α · β) + (vk_x_val · γ) + (c_val · δ)   in Fr
--
--   Expanding a_val, b_val, vk_x_val, c_val and collecting terms, this
--   reduces to QAPSat (i.e. (Σ aᵢuᵢ)(Σ aᵢvᵢ) = Σ aᵢwᵢ + h·t).
--
--   Blocked on: simp/ring lemmas for pairing_smul_compat + vkX vs mkIC
--               correspondence under the list structure.

lemma honest_prover_pairing_eq
    (pd    : PairingData Fr G1 G2 GT)
    (crs   : CRS Fr)
    (qap   : QAPEval Fr)
    (all   : List Fr)
    (n_pub : ℕ)
    (r s   : Fr)
    (h_qap : QAPSat qap all) :
    Groth16Valid pd
      (mkVk g1 g2 crs qap n_pub)
      (honestProver g1 g2 crs qap all n_pub r s)
      (all.take n_pub) := by
  simp only [Groth16Valid, honestProver, mkVk, vkX, pairing_smul_compat]
  -- After applying pairing_smul_compat on each pairing and collecting via
  -- bilin_left, both sides reduce to pd.pairing (scalar • g1) g2 for the
  -- same scalar, which holds by the Fr ring identity implied by h_qap.
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- MAIN THEOREM
-- ─────────────────────────────────────────────────────────────────────────────

/-- The honest prover is always accepted, given R1CS satisfaction and
    that the verifying key matches the QAP (well-formedness). -/
theorem concrete_prover_correct
    (pd      : PairingData Fr G1 G2 GT)
    (crs     : CRS Fr)
    (R1CS    : R1CSRelation Fr)
    (qap     : QAPEval Fr)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_r1cs  : R1CS inputs witness)
    (h_wf    : wellFormed Fr G1 G2 (mkVk g1 g2 crs qap inputs.length) inputs) :
    verifyGroth16 pd
      (mkVk g1 g2 crs qap inputs.length)
      (honestProver g1 g2 crs qap (inputs ++ witness) inputs.length r s)
      inputs = true := by
  rw [verifyGroth16_correct pd _ _ inputs h_wf]
  have h_qap := r1cs_implies_qap_sat R1CS qap inputs witness h_r1cs
  have h_eq  := honest_prover_pairing_eq g1 g2 pd crs qap
                  (inputs ++ witness) inputs.length r s h_qap
  simp only [List.take_left] at h_eq
  exact h_eq

end Groth16Verifier.Properties.CompletenessProver
