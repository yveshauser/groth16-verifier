-- Groth16Verifier.Properties.CompletenessProver
--
-- The four steps follow Groth 2016, §3 closely.

import Groth16Verifier.Properties.Correctness
import Mathlib.Tactic.LinearCombination

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
--   (u₀ + Σᵢ aᵢ·uᵢ₊₁) · (v₀ + Σᵢ aᵢ·vᵢ₊₁) = (w₀ + Σᵢ aᵢ·wᵢ₊₁) + h·t
-- where wire 0 has implicit constant coefficient 1, and a₁..aₘ are the
-- explicit wire assignments.

structure QAPEval (Fr : Type*) [Field Fr] where
  -- Evaluated polynomials, one entry per wire (length = m+1).
  u  : List Fr   -- uᵢ(τ)
  v  : List Fr   -- vᵢ(τ)
  w  : List Fr   -- wᵢ(τ)
  t  : Fr        -- t(τ)
  h  : Fr        -- h(τ)
  /-- All three polynomial lists have the same length (one entry per wire). -/
  h_uv : u.length = v.length
  h_vw : v.length = w.length

-- Weighted inner product: Σᵢ aᵢ · bᵢ  (lists are truncated to the shorter)
private def wsum (a b : List Fr) : Fr := (zipWith (· * ·) a b).sum

-- QAP satisfiability for assignment a = inputs ++ witness, with implicit
-- constant wire (a₀ = 1).  The QAPEval stores one extra evaluation at
-- index 0 for the constant wire; a[i] is the coefficient of wire i+1.
-- QAPSat qap a  ⟺  (u₀ + Σᵢ aᵢ·uᵢ₊₁) · (v₀ + Σᵢ aᵢ·vᵢ₊₁) = (w₀ + Σᵢ aᵢ·wᵢ₊₁) + h·t
def QAPSat (qap : QAPEval Fr) (a : List Fr) : Prop :=
  (qap.u.getD 0 0 + wsum a qap.u.tail) * (qap.v.getD 0 0 + wsum a qap.v.tail) =
  (qap.w.getD 0 0 + wsum a qap.w.tail) + qap.h * qap.t


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
--   A = (α + u₀ + Σ aᵢ uᵢ₊₁(τ) + r·δ) · g1
--   B = (β + v₀ + Σ aᵢ vᵢ₊₁(τ) + s·δ) · g2
--   C = ((Σ_{priv i} aᵢ (β·uᵢ + α·vᵢ + wᵢ)(τ) + h(τ)·t(τ)) / δ
--         + s·A_val + r·B_val − r·s·δ) · g1
--
-- Wire 0 is always the constant wire with implicit coefficient 1, so the
-- sum starts from u₀ = u.getD 0 0 (constant) and then Σ aᵢ · u.tail[i].
-- Private wires start at index n_pub+1 (index n_pub is the last public wire),
-- so we drop (n_pub+1) elements from the polynomial lists.

def honestProver
    (crs   : CRS Fr)
    (qap   : QAPEval Fr)
    (all   : List Fr)   -- inputs ++ witness  (full assignment)
    (n_pub : ℕ)         -- = inputs.length
    (r s   : Fr) :
    Proof G1 G2 :=
  -- a_val = α + u₀ + Σ aᵢ·uᵢ₊₁ + r·δ  (constant wire u₀ + all wire sum)
  let a_val := crs.alpha + qap.u.getD 0 0 + wsum all qap.u.tail + r * crs.delta
  let b_val := crs.beta  + qap.v.getD 0 0 + wsum all qap.v.tail + s * crs.delta
  -- Private-wire numerator: Σ_{i > n_pub} aᵢ (β·uᵢ + α·vᵢ + wᵢ)(τ)
  -- Private witnesses are all.drop n_pub; private polys start at index n_pub+1.
  let priv      := all.drop n_pub
  let priv_ic_u := qap.u.drop (n_pub + 1) |>.map (crs.beta  * ·)
  let priv_ic_v := qap.v.drop (n_pub + 1) |>.map (crs.alpha * ·)
  let priv_ic_w := qap.w.drop (n_pub + 1)
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
-- Proof sketch:
--  1. Unfold definitions; apply pairing_smul_compat to pure-smul pairings.
--  2. Move γ from G2 to G1 for the vkX term via scalar_compat.
--  3. Express vkX (mkVk ...) as a scalar × g1 using vkX_mkVk_eq_smul.
--  4. Merge RHS pairings via bilin_left + add_smul.
--  5. Reduce to the scalar identity: a_val·b_val = α·β + γ·vkx_s + c_val·δ.
--  6. This identity reduces to QAPSat by ring + simp.

-- ── Helper lemmas ─────────────────────────────────────────────────────────────

-- range (n+1) = 0 :: (range n).map (·+1)
private lemma range_succ_cons (n : ℕ) :
    List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [List.range_succ, ih]
    rw [List.range_succ, List.map_append, List.map_singleton]
    simp [List.cons_append]

-- wsum distributes over zipWith (+)
-- Requires b.length = c.length; otherwise the claim is false (zipWith truncates).
omit [DecidableEq Fr] in
private lemma wsum_zipWith_add (a b c : List Fr) (h : b.length = c.length) :
    wsum a (List.zipWith (· + ·) b c) = wsum a b + wsum a c := by
  simp only [wsum]
  induction b generalizing a c with
  | nil =>
    cases c with
    | nil => simp
    | cons z zs => simp at h
  | cons y ys ih =>
    cases c with
    | nil => simp at h
    | cons z zs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      cases a with
      | nil => simp
      | cons x xs =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        rw [ih xs zs h]; ring

-- scalar factors out of wsum (right list)
private lemma wsum_mul_left (k : Fr) (a b : List Fr) :
    wsum a (b.map (k * ·)) = k * wsum a b := by
  simp only [wsum]
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [ih]; ring

-- wsum distributes over pointwise triple-addition on an indexed list
omit [DecidableEq Fr] in
private lemma wsum_map_add3 {ι : Type*} (a : List Fr) (l : List ι) (f g h : ι → Fr) :
    wsum a (l.map (fun i => f i + g i + h i)) =
    wsum a (l.map f) + wsum a (l.map g) + wsum a (l.map h) := by
  simp only [wsum]
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [ih ys]; ring

-- scalar factors out of wsum over an indexed list
omit [DecidableEq Fr] in
private lemma wsum_map_smul {ι : Type*} (k : Fr) (a : List Fr) (l : List ι) (f : ι → Fr) :
    wsum a (l.map (fun i => k * f i)) = k * wsum a (l.map f) := by
  simp only [wsum]
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [ih ys]; ring

-- (l.map (· • g)).sum = l.sum • g
private lemma sum_smul_list (l : List Fr) (g : G1) :
    (l.map (· • g)).sum = l.sum • g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_smul]

-- (zipWith (·•·) xs (ys.map (·•g))).sum = wsum xs ys • g
private lemma zipWith_smul_smul_sum (xs : List Fr) (ys : List Fr) (g : G1) :
    (List.zipWith (· • ·) xs (ys.map (· • g))).sum = wsum xs ys • g := by
  simp only [wsum]
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [smul_smul, ih, ← add_smul]

-- wsum (a.take n) l + wsum (a.drop n) (l.drop n) = wsum a l
omit [DecidableEq Fr] in
private lemma wsum_take_drop (a l : List Fr) (n : ℕ) :
    wsum (a.take n) l + wsum (a.drop n) (l.drop n) = wsum a l := by
  simp only [wsum]
  induction a generalizing l n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases l with
      | nil => simp
      | cons y ys =>
        simp only [List.take_succ_cons, List.drop_succ_cons, List.zipWith_cons_cons, List.sum_cons]
        rw [add_assoc, ih ys n]

-- l.drop (n+1) = l.tail.drop n
private lemma drop_succ_eq_tail_drop (l : List Fr) (n : ℕ) :
    l.drop (n + 1) = l.tail.drop n := by
  cases l with
  | nil => simp
  | cons x xs => simp [List.drop_succ_cons]

-- wsum a ((range n).map (fun i => l.getD (i+1) 0)) = wsum a l.tail
-- Holds because a.length ≤ n ensures truncation only cuts at a.length,
-- and l.getD (i+1) 0 = l.tail.getD i 0 (zero outside l.tail's range is
-- consistent with zipWith truncating to the shorter list).
omit [DecidableEq Fr] in
private lemma wsum_range_getD_eq (a l : List Fr) (n : ℕ) (hn : a.length ≤ n) :
    wsum a ((List.range n).map (fun i => l.getD (i + 1) 0)) = wsum a l.tail := by
  simp only [wsum]
  induction a generalizing l n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at hn
    | succ n' =>
      have hn' : xs.length ≤ n' := by simp [List.length_cons] at hn; omega
      rw [range_succ_cons n', List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      -- ((range n').map (+1)).map (fun i => l.getD (i+1) 0) = (range n').map (fun i => l.tail.getD (i+1) 0)
      -- Proof: compose the maps (map_map), then shift getD index via l.getD (i+1+1) 0 = l.tail.getD (i+1) 0.
      -- We keep map_map inside hmap's proof to avoid normalising l.getD → l[·]?.getD in the main goal.
      have hmap : ((List.range n').map (· + 1)).map (fun i => l.getD (i + 1) (0 : Fr)) =
                  (List.range n').map (fun i => l.tail.getD (i + 1) 0) := by
        have hf : (fun i => l.getD (i + 1) (0 : Fr)) ∘ (· + 1) = fun i => l.tail.getD (i + 1) 0 :=
          funext fun i => by cases l with | nil => simp | cons y ys => simp
        rw [List.map_map, hf]
      -- l.getD 1 0 = l.tail.getD 0 0
      have h1 : l.getD 1 (0 : Fr) = l.tail.getD 0 0 := by
        cases l with | nil => simp | cons y ys => simp
      rw [hmap, ih l.tail n' hn', h1]
      cases l.tail with
      | nil => simp
      | cons z zs => simp [List.zipWith_cons_cons, List.sum_cons]

-- icScalar i * γ = β·u[i] + α·v[i] + w[i]
private lemma icScalar_mul_gamma (crs : CRS Fr) (qap : QAPEval Fr) (i : ℕ) :
    icScalar crs qap i * crs.gamma =
    crs.beta * qap.u.getD i 0 + crs.alpha * qap.v.getD i 0 + qap.w.getD i 0 := by
  simp only [icScalar]
  simp_all [crs.h_gamma]

-- vkX of mkVk is a scalar multiple of g1:
--   vkX (mkVk g1 g2 crs qap n_pub) inputs
--   = (icScalar 0 + wsum inputs ((range n_pub).map (fun i => icScalar (i+1)))) • g1
private lemma vkX_mkVk_eq_smul
    (crs : CRS Fr) (qap : QAPEval Fr) (n_pub : ℕ) (inputs : List Fr) :
    vkX (mkVk g1 g2 crs qap n_pub) inputs =
      (icScalar crs qap 0 +
       wsum inputs ((List.range n_pub).map (fun i => icScalar crs qap (i + 1)))) • g1 := by
  simp only [vkX, mkVk, mkIC, range_succ_cons, List.map_cons, List.head_cons, List.tail_cons,
             List.map_map, Function.comp_def]
  rw [show (List.range n_pub).map (fun x => icScalar crs qap (x + 1) • g1) =
      ((List.range n_pub).map (fun x => icScalar crs qap (x + 1))).map (· • g1) from by
    simp [List.map_map]]
  rw [zipWith_smul_smul_sum, add_smul]

-- ── Main pairing-equation lemma ────────────────────────────────────────────────
--
-- Algebraic identity: after substituting the honest prover's outputs and the
-- verifying key into the Groth16 equation, both sides equal
--
--   pd.pairing ((a_val * b_val) • g1) g2
--
-- where the scalar identity  a_val * b_val = α·β + γ·vkx_s + c_val·δ
-- reduces to QAPSat by ring + simp.

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
  -- ① Unfold the validity predicate and prover outputs
  --    Do NOT include mkVk here: fully unfolding it would replace
  --    vkX (mkVk …) with vkX {…}, breaking the pattern match in step ③.
  simp only [Groth16Valid, honestProver]
  -- Expose the four VK fields (projections) without unfolding mkVk wholesale
  rw [show (mkVk g1 g2 crs qap n_pub).alpha = crs.alpha • g1 from rfl,
      show (mkVk g1 g2 crs qap n_pub).beta  = crs.beta  • g2 from rfl,
      show (mkVk g1 g2 crs qap n_pub).gamma = crs.gamma • g2 from rfl,
      show (mkVk g1 g2 crs qap n_pub).delta = crs.delta • g2 from rfl]
  -- ② Apply pairing_smul_compat to the three pure-smul pairings
  --    (A,B), (alpha,beta), (C,delta) — but NOT the middle vkX term.
  simp only [pairing_smul_compat pd]
  -- After this, LHS = pd.pairing ((a_val * b_val) • g1) g2
  --              RHS = pd.pairing ((α * β) • g1) g2
  --                  * pd.pairing (vkX ...) (γ • g2)
  --                  * pd.pairing ((c_val * δ) • g1) g2
  -- ③ Move γ from G2 side to G1 side for the vkX term
  rw [← pd.scalar_compat crs.gamma (vkX (mkVk g1 g2 crs qap n_pub) (all.take n_pub)) g2]
  -- ④ Express vkX as a scalar multiple of g1
  rw [vkX_mkVk_eq_smul g1 g2 crs qap n_pub (all.take n_pub)]
  -- ⑤ Merge scalar smuls: γ • (vkx_s • g1) = (γ * vkx_s) • g1
  rw [smul_smul]
  -- ⑥ Merge the three RHS pairings via bilinearity
  rw [← pd.bilin_left, ← add_smul, ← pd.bilin_left, ← add_smul]
  -- Goal is now:
  --   pd.pairing ((a_val * b_val) • g1) g2
  --   = pd.pairing ((α*β + γ*vkx_s + c_val*δ) • g1) g2
  -- ⑦ Reduce to the scalar identity
  apply congr_arg (fun s => pd.pairing (s • g1) g2)
  -- Goal: a_val * b_val = α*β + γ*vkx_s + c_val*δ
  -- ⑧ Prove the scalar identity
  --
  -- Key intermediate facts needed:
  --   (a) priv_sum = β·U_priv + α·V_priv + W_priv
  --   (b) γ·vkx_s  = β·(u₀+pub_U) + α·(v₀+pub_V) + (w₀+pub_W)
  --   (c) pub_X + X_priv = wsum all qap.X.tail   (take-drop split)
  --   (d) c_val · δ clears the division
  --
  -- Together these reduce the goal to QAPSat via ring.
  -- Name sub-expressions for clarity
  set α   := crs.alpha
  set β   := crs.beta
  set γ   := crs.gamma
  set δ   := crs.delta
  set u₀  := qap.u.getD 0 0
  set v₀  := qap.v.getD 0 0
  set w₀  := qap.w.getD 0 0
  set U   := wsum all qap.u.tail
  set V   := wsum all qap.v.tail
  set W   := wsum all qap.w.tail
  set prv := all.drop n_pub
  set U_p := wsum prv (qap.u.drop (n_pub + 1))   -- private U
  set V_p := wsum prv (qap.v.drop (n_pub + 1))   -- private V
  set W_p := wsum prv (qap.w.drop (n_pub + 1))   -- private W
  -- Public sums (in range-getD form from vkX computation)
  set pub_U := wsum (all.take n_pub) ((List.range n_pub).map fun i => qap.u.getD (i + 1) 0)
  set pub_V := wsum (all.take n_pub) ((List.range n_pub).map fun i => qap.v.getD (i + 1) 0)
  set pub_W := wsum (all.take n_pub) ((List.range n_pub).map fun i => qap.w.getD (i + 1) 0)
  -- (a) priv_sum in terms of U_p, V_p, W_p
  have h_priv :
      wsum prv (List.zipWith (· + ·)
        (List.zipWith (· + ·)
          (qap.u.drop (n_pub + 1) |>.map (β * ·))
          (qap.v.drop (n_pub + 1) |>.map (α * ·)))
        (qap.w.drop (n_pub + 1))) = β * U_p + α * V_p + W_p := by
    simp only [U_p, V_p, W_p]
    -- Bring length-equality fields into the local context so omega can use them.
    have huv : qap.u.length = qap.v.length := qap.h_uv
    have hvw : qap.v.length = qap.w.length := qap.h_vw
    -- Length proofs needed by wsum_zipWith_add (zipWith truncates to the shorter list,
    -- so equality of lengths is required for the identity to hold).
    have hlen_uv : (qap.u.drop (n_pub + 1) |>.map (β * ·)).length =
                   (qap.v.drop (n_pub + 1) |>.map (α * ·)).length := by
      simp only [List.length_map, List.length_drop]; omega
    have hlen_uvw : (List.zipWith (· + ·)
                      (qap.u.drop (n_pub + 1) |>.map (β * ·))
                      (qap.v.drop (n_pub + 1) |>.map (α * ·))).length =
                    (qap.w.drop (n_pub + 1)).length := by
      simp only [List.length_zipWith, List.length_map, List.length_drop]; omega
    rw [wsum_zipWith_add _ _ _ hlen_uvw, wsum_zipWith_add _ _ _ hlen_uv,
        wsum_mul_left, wsum_mul_left]
  -- (b) γ · vkx_s  (clearing the 1/γ in icScalar)
  --  γ · (icScalar 0 + wsum inputs (...)) = (β·u₀+α·v₀+w₀) + β·pub_U + α·pub_V + pub_W
  have h_vkx :
      γ * (icScalar crs qap 0 +
           wsum (all.take n_pub) ((List.range n_pub).map fun i => icScalar crs qap (i + 1))) =
      β * (u₀ + pub_U) + α * (v₀ + pub_V) + (w₀ + pub_W) := by
    -- γ * icScalar crs qap i = β * u[i] + α * v[i] + w[i]  (clearing the /γ)
    have key : ∀ i, γ * icScalar crs qap i =
        β * qap.u.getD i 0 + α * qap.v.getD i 0 + qap.w.getD i 0 := fun i => by
      rw [mul_comm]; exact icScalar_mul_gamma crs qap i
    -- γ distributes into the wsum, then ics_γ rewrites each entry entry-wise
    have h_sum : γ * wsum (all.take n_pub) ((List.range n_pub).map fun i => icScalar crs qap (i + 1)) =
        β * pub_U + α * pub_V + pub_W := by
      rw [← wsum_mul_left, List.map_map]
      have hmaps : (List.range n_pub).map ((fun x => γ * x) ∘ fun i => icScalar crs qap (i + 1)) =
          (List.range n_pub).map (fun i =>
            β * qap.u.getD (i + 1) 0 + α * qap.v.getD (i + 1) 0 + qap.w.getD (i + 1) 0) := by
        congr 1; ext i; exact key (i + 1)
      rw [hmaps, wsum_map_add3, wsum_map_smul, wsum_map_smul]
    -- Distribute γ, substitute h_sum, unfold the set variables u₀/v₀/w₀, apply key 0, ring
    rw [mul_add, h_sum,
        show u₀ = qap.u.getD 0 0 from rfl,
        show v₀ = qap.v.getD 0 0 from rfl,
        show w₀ = qap.w.getD 0 0 from rfl,
        key 0]
    ring
  -- (c) pub_X + X_p = wsum all qap.X.tail  (take-drop split for U, V, W)
  have h_pu_eq : pub_U = wsum (all.take n_pub) qap.u.tail :=
    wsum_range_getD_eq (all.take n_pub) qap.u n_pub (List.length_take_le n_pub all)
  have h_pv_eq : pub_V = wsum (all.take n_pub) qap.v.tail :=
    wsum_range_getD_eq (all.take n_pub) qap.v n_pub (List.length_take_le n_pub all)
  have h_pw_eq : pub_W = wsum (all.take n_pub) qap.w.tail :=
    wsum_range_getD_eq (all.take n_pub) qap.w n_pub (List.length_take_le n_pub all)
  have h_su : pub_U + U_p = U := by
    simp only [U, U_p, pub_U, h_pu_eq]
    rw [drop_succ_eq_tail_drop, wsum_take_drop]
  have h_sv : pub_V + V_p = V := by
    simp only [V, V_p, pub_V, h_pv_eq]
    rw [drop_succ_eq_tail_drop, wsum_take_drop]
  have h_sw : pub_W + W_p = W := by
    simp only [W, W_p, pub_W, h_pw_eq]
    rw [drop_succ_eq_tail_drop, wsum_take_drop]
  -- (d) Clear the division in c_val · δ
  have h_cδ :
      ((wsum prv (List.zipWith (· + ·)
          (List.zipWith (· + ·)
            (qap.u.drop (n_pub + 1) |>.map (β * ·))
            (qap.v.drop (n_pub + 1) |>.map (α * ·)))
          (qap.w.drop (n_pub + 1))) + qap.h * qap.t) / δ +
       s * (α + u₀ + U + r * δ) +
       r * (β + v₀ + V + s * δ) -
       r * s * δ) * δ =
      β * U_p + α * V_p + W_p + qap.h * qap.t +
      s * (α + u₀ + U + r * δ) * δ +
      r * (β + v₀ + V + s * δ) * δ -
      r * s * δ ^ 2 := by
    rw [h_priv]
    have hδ : δ ≠ 0 := crs.h_delta
    rw [sub_mul, add_mul, add_mul, div_mul_cancel₀ _ hδ]
    ring
  -- (e) Main scalar identity: expand all definitions and apply h_qap
  -- After substituting h_vkx and h_priv, the identity is:
  --   (α + u₀ + U + r·δ) · (β + v₀ + V + s·δ)
  --   = α·β + β·(u₀+pub_U) + α·(v₀+pub_V) + (w₀+pub_W)
  --     + β·U_p + α·V_p + W_p + h·t + ZK_terms
  -- Using pub_X + X_p = X, this collapses to:
  --   (α + u₀ + U + r·δ) · (β + v₀ + V + s·δ) = α·β + β·(u₀+U) + α·(v₀+V) + (w₀+W) + h·t + ZK
  -- After cancellation of ZK terms: U·V = W + h·t  ← exactly QAPSat.
  -- Substitute c_val·δ (clearing the /δ) and γ·vkx_s (clearing the /γ in icScalar).
  -- What remains is a polynomial identity in Fr, discharged by ring + QAPSat.
  rw [h_cδ, h_vkx]
  -- Restate h_qap with the set-variable names so linear_combination can see it as an equation.
  -- (QAPSat qap all is opaque to the ring checker; an explicit equation is not.)
  have h_qap' : (u₀ + U) * (v₀ + V) = (w₀ + W) + qap.h * qap.t := h_qap
  linear_combination h_qap' - α * h_sv - β * h_su - h_sw

-- ─────────────────────────────────────────────────────────────────────────────
-- MAIN THEOREM
-- ─────────────────────────────────────────────────────────────────────────────

/-- The honest prover is always accepted, given QAP satisfaction and
    that the verifying key matches the QAP (well-formedness). -/
theorem concrete_prover_correct
    (pd      : PairingData Fr G1 G2 GT)
    (crs     : CRS Fr)
    (qap     : QAPEval Fr)
    (inputs  : List Fr)
    (witness : List Fr)
    (r s     : Fr)
    (h_qap   : QAPSat qap (inputs ++ witness))
    (h_wf    : wellFormed Fr G1 G2 (mkVk g1 g2 crs qap inputs.length) inputs) :
    verifyGroth16 pd
      (mkVk g1 g2 crs qap inputs.length)
      (honestProver g1 g2 crs qap (inputs ++ witness) inputs.length r s)
      inputs = true := by
  rw [verifyGroth16_correct pd _ _ inputs h_wf]
  have h_eq := honest_prover_pairing_eq g1 g2 pd crs qap
                 (inputs ++ witness) inputs.length r s h_qap
  simp only [List.take_left] at h_eq
  exact h_eq

end Groth16Verifier.Properties.CompletenessProver
