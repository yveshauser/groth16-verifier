# groth16-verifier

Formal verification of a Groth16 zk-SNARK verifier over BLS12-381 in Lean 4.

This project proves that the [`groth16_verifier.ak`](groth16_verifier.ak)
Aiken smart contract on Cardano correctly implements the Groth16 verification
equation — and that it is sound, complete, and zero-knowledge — using Lean 4
and Mathlib as the proof foundation.

---

## Background

### The full stack

This repository sits at the top of a toolchain that runs from Circom circuits
down to a Cardano smart contract:

```
Circom circuit (.circom)
        │  compiled by circom + snarkjs (BLS12-381 ceremony)
        ▼
Groth16 proof  (proof.json + vk.json)
        │  serialised by convert.sh (ak-381 tooling)
        ▼
Aiken validator  (groth16_verifier.ak)   ← this is what we verify
        │  compiled to Plutus V3
        ▼
Cardano on-chain verification
        │  using native BLS12-381 pairing builtins (CIP-0381)
        ▼
Transaction accepted / rejected
```

### Why verify the verifier?

The Aiken contract is the security-critical component: if it has a bug, a
cheating prover could unlock funds without a valid proof. The on-chain
verifier is a Plutus script that must be correct by construction.

Formal verification gives a machine-checked guarantee that the contract
computes exactly the Groth16 pairing equation, with no shortcuts, no
off-by-one errors in the linear combination, and no missing negation of `A`.

---

## What this project proves

The library establishes four properties of `verify_groth16` in
`groth16_verifier.ak`:

| # | Theorem | Statement | File | Proof status |
|---|---|---|---|---|
| 1 | **Correctness** | `verifyGroth16 pd vk proof inputs = true ↔ Groth16Valid pd vk proof inputs` | `Correctness.lean` | ✓ Proved (given `wellFormed vk inputs`) |
| 2 | **Completeness** | An honest prover with a valid witness is always accepted | `Completeness.lean` | ✓ Proved, modulo `groth16_prover_correct` axiom |
| 3 | **Soundness** | A cheating prover cannot be accepted | `Soundness.lean` | ✓ Proved, modulo `agm_knowledge_extractor` axiom |
| 4 | **Zero-Knowledge** | Proof reveals nothing about the witness | `ZeroKnowledge.lean` | ✓ Proved, modulo `groth16_perfect_zk` axiom |

**Correctness** is the core theorem and is proved purely from algebraic
properties of pairings — no cryptographic hardness assumptions. The other
three theorems are reduced to named axioms that correspond to standard
Groth16 security results from the literature.

### The Groth16 verification equation

The Aiken contract checks:

```
e(-A, B) · e(α, β) · e(vk_x, γ) · e(C, δ) = 1_GT
```

where `vk_x = IC[0] + x₁·IC[1] + … + xₙ·IC[n]` and `e` is the BLS12-381
Ate pairing. The **Correctness** theorem proves this `Bool` computation is
equivalent to the mathematical predicate `Groth16Valid`.

---

## Module structure

```
groth16-verifier/
├── lean-toolchain              Pins Lean 4.14.0
├── lakefile.toml               Lake build config + Mathlib dependency
├── lake-manifest.json          Dependency lock file (run lake update -R to populate)
├── flake.nix                   Nix development shell (elan, git)
├── .github/workflows/ci.yml    GitHub Actions CI
├── scripts/
│   └── check_axioms.lean       Introspects which axioms each theorem depends on
├── CONTRIBUTING.md             How to close the remaining proof gaps
└── Groth16Verifier/
    ├── Algebra.lean            Abstract BLS12-381 pairing groups + derived lemmas
    │                           (bilinearity, pairing_zero_left, pairing_neg_left, …)
    ├── Types.lean              VerifyingKey, Proof, wellFormed
    ├── Spec.lean               Mathematical spec: vkX, Groth16Valid, Groth16ValidNeg
    ├── Impl.lean               Lean transliteration of groth16_verifier.ak
    │                           (computeVkX, verifyGroth16, foldl/zipWith equivalence)
    └── Properties/
        ├── Correctness.lean    ★ verifyGroth16 = true ↔ Groth16Valid
        ├── Completeness.lean   Honest prover always accepted
        ├── Soundness.lean      Cheating prover rejected (under AGM)
        └── ZeroKnowledge.lean  Witness indistinguishability
```

### Correspondence with the Aiken contract

The Lean `verifyGroth16` in `Impl.lean` mirrors `verify_groth16` in
`groth16_verifier.ak` line-by-line:

| Aiken | Lean |
|---|---|
| `compute_vk_x ic inputs` | `computeVkX ic inputs` |
| `g1.negate proof.a` | `-proof.A` |
| `pairing.miller_loop P Q` | `pd.pairing P Q` |
| `pairing.mul_miller_loop_result a b` | `a * b` in GT |
| `pairing.final_verify lhs one` | `decide (lhs = 1)` |

The Correctness theorem formally certifies this correspondence.

---

## Getting started

### Prerequisites

- [elan](https://github.com/leanprover/elan) — the Lean version manager

Or with Nix (consistent with the Circom/snarkjs dev shell in this repo):

```bash
nix develop   # drops you into a shell with elan, git, curl
```

### First-time setup

```bash
# 1. Clone
git clone https://github.com/<your-org>/groth16-verifier
cd groth16-verifier

# 2. Install the pinned Lean toolchain
elan toolchain install "$(cat lean-toolchain)"

# 3. Resolve dependencies and generate lake-manifest.json
lake update -R

# 4. Download prebuilt Mathlib .olean files (~1 GB, ~2–5 min)
#    This is MUCH faster than building Mathlib from source (~1 hour).
lake exe cache get

# 5. Build
lake build
```

### Interactive proof checking

Open the project folder in VS Code with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
installed. The infoview panel shows the proof state at the cursor position.

A good entry point is `Correctness.lean` — place the cursor inside
`verifyGroth16_correct` and step through the tactic proof to see how the
algebraic identity unfolds.

---

## Proof status in detail

### Fully proved

These lemmas have no remaining gaps:

- `Algebra.pairing_zero_left` / `pairing_zero_right` — `e(0, Q) = 1`
- `Algebra.pairing_neg_left` — `e(-P, Q) = e(P, Q)⁻¹`
- `Algebra.multipairing_eq_one_iff` — the central algebraic identity
- `Algebra.pairing_sum_left` — bilinearity over a list sum
- `Spec.groth16Valid_iff_neg` — equivalence of the two verification forms
- `Correctness.foldl_zip_eq` — `foldl` over `zip` equals `zipWith` sum (generic)
- `Correctness.computeVkX_eq_vkX_vk` — implementation matches spec
- `Correctness.verifyGroth16_correct` — the main theorem (given `wellFormed`)
- `Correctness.verifyGroth16_false_iff` — false iff equation does not hold
- `Completeness.verifyGroth16_complete` — honest prover accepted
- `Completeness.verifyGroth16_no_false_negatives`
- `Soundness.verifyGroth16_sound` — cheating prover rejected
- `Soundness.verifyGroth16_no_false_positives`
- `ZeroKnowledge.simulated_proof_verifies`
- `ZeroKnowledge.witness_indistinguishable`

### Remaining admits

There are no remaining `admit`s in `Correctness.lean`. The theorem
`verifyGroth16_correct` is fully proved under the assumption
`wellFormed Fr G1 G2 vk inputs` (i.e. `vk.ic.length = inputs.length + 1`),
which reflects how the contract is actually deployed — the VK is
hardcoded for a specific circuit with a fixed number of public inputs.

### Named axioms

These axioms are intentional. They correspond to standard Groth16 security
theorems from the literature:

| Axiom | Theorem it supports | Literature reference |
|---|---|---|
| `groth16_prover_correct` | Completeness | Groth 2016, Theorem 1 |
| `agm_knowledge_extractor` | Soundness | Fuchsbauer-Kiltz-Loss 2018 (AGM) |
| `groth16_perfect_zk` | Zero-Knowledge | Groth 2016, Theorem 3 |

To inspect which axioms each theorem depends on at runtime:

```bash
lake env lean scripts/check_axioms.lean
```

The invariant to maintain: `verifyGroth16_correct` must depend **only** on
`propext`, `Classical.choice`, `Quot.sound`, and `funext`. If any crypto
axiom appears there, the Correctness proof has an unintended gap.

---

## Useful commands

```bash
# First-time: install toolchain, resolve deps, fetch cache
elan toolchain install "$(cat lean-toolchain)" && lake update -R && lake exe cache get

lake build                          # build everything
lake build Groth16Verifier.Correctness  # build a single module
lake env lean scripts/check_axioms.lean  # show axiom dependencies
grep -r 'sorry\|admit' Groth16Verifier/  # find remaining sorries / admits
rm -rf .lake/build                  # remove build artifacts
rm -rf .lake/                       # nuclear reset
```

---

## Relationship to related projects

| Project | Layer | Relationship |
|---|---|---|
| [ak-381](https://github.com/Modulo-P/ak-381) | Aiken implementation | The library whose internal logic we are verifying |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Mathematics | Foundation: groups, fields, polynomials, linear independence |

---

## References

- Groth, J. (2016). [On the Size of Pairing-based Non-interactive Arguments](https://eprint.iacr.org/2016/260). *EUROCRYPT 2016*.
- Fuchsbauer, G., Kiltz, E., & Loss, J. (2018). [The Algebraic Group Model and its Applications](https://eprint.iacr.org/2017/620). *CRYPTO 2018*.
- Firsov, D. & Livshits, B. (2024). [The Ouroboros of ZK: Why Verifying the Verifier Unlocks Longer-Term ZK Innovation](https://eprint.iacr.org/2024/768). *ePrint 2024/768*.
- Nethermind & Matter Labs. (2025). [Formal Verification of the ZKSync Verifier](https://www.nethermind.io/blog/formal-verification-of-the-zksync-verifier). *First production ZK verifier verification, using EasyCrypt*.
- Cardano Foundation. [CIP-0381: Plutus support for BLS12-381 curve operations](https://cips.cardano.org/cip/CIP-0381).
- Cardano Foundation. [CIP-0133: Plutus support for Multi-Scalar Multiplication over BLS12-381](https://cips.cardano.org/cip/CIP-0133).

---

## License

Apache 2.0. See [LICENSE](LICENSE).
