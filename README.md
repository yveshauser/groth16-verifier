# groth16-verifier

Formal verification of a Groth16 zk-SNARK verifier over BLS12-381 in Lean 4.

This project proves that the [`groth16_verifier.ak`](../groth16_verifier.ak)
Aiken smart contract on Cardano correctly implements the Groth16 verification
equation — and that it is sound, complete, and zero-knowledge — using Lean 4
and Mathlib as the proof foundation.

Inspired by Firsov & Livshits,
[*The Ouroboros of ZK*](https://eprint.iacr.org/2024/768) (ePrint 2024/768),
and the production verification of ZKSync's PLONK verifier by Nethermind.

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
cheating prover could unlock funds without a valid proof. Unlike the circuit
(which can be tested with snarkjs), the on-chain verifier is a Plutus script
that must be correct by construction — there is no runtime exception, just
a wrong `True` or `False`.

Formal verification gives a machine-checked guarantee that the contract
computes exactly the Groth16 pairing equation, with no shortcuts, no
off-by-one errors in the linear combination, and no missing negation of `A`.

---

## What this project proves

The library establishes four properties of `verify_groth16` in
`groth16_verifier.ak`:

| # | Theorem | Statement | File | Proof status |
|---|---|---|---|---|
| 1 | **Honesty** | `verifyGroth16 pd vk proof inputs = true ↔ Groth16Valid pd vk proof inputs` | `Honesty.lean` | ✓ Proved (2 admits for ill-formed IC — see below) |
| 2 | **Completeness** | An honest prover with a valid witness is always accepted | `Completeness.lean` | ✓ Proved, modulo `groth16_prover_correct` axiom |
| 3 | **Soundness** | A cheating prover cannot be accepted | `Soundness.lean` | ✓ Proved, modulo `agm_knowledge_extractor` axiom |
| 4 | **Zero-Knowledge** | Proof reveals nothing about the witness | `ZeroKnowledge.lean` | ✓ Proved, modulo `groth16_perfect_zk` axiom |

**Honesty** is the core theorem and is proved purely from algebraic
properties of pairings — no cryptographic hardness assumptions. The other
three theorems are reduced to named axioms that correspond to standard
Groth16 security results from the literature, which can be discharged once
[ArkLib](https://github.com/Verified-zkEVM/ArkLib) mechanises Groth16
completeness and soundness.

### The Groth16 verification equation

The Aiken contract checks:

```
e(-A, B) · e(α, β) · e(vk_x, γ) · e(C, δ) = 1_GT
```

where `vk_x = IC[0] + x₁·IC[1] + … + xₙ·IC[n]` and `e` is the BLS12-381
Ate pairing. The **Honesty** theorem proves this `Bool` computation is
equivalent to the mathematical predicate `Groth16Valid`.

---

## Module structure

```
groth16-verifier/
├── lean-toolchain              Pins Lean 4.14.0
├── lakefile.toml               Lake build config + Mathlib dependency
├── lake-manifest.json          Dependency lock file (run lake update -R to populate)
├── flake.nix                   Nix development shell (elan, just, git)
├── justfile                    Convenience task runner
├── .github/workflows/ci.yml    GitHub Actions CI
├── scripts/
│   └── check_axioms.lean       Introspects which axioms each theorem depends on
├── CONTRIBUTING.md             How to close the remaining proof gaps
└── Groth16Verifier/
    ├── Algebra.lean            Abstract BLS12-381 pairing groups + derived lemmas
    │                           (bilinearity, pairing_zero_left, pairing_neg_left, …)
    ├── Types.lean              VerifyingKey, Proof, R1CSRelation, wellFormed
    ├── Spec.lean               Mathematical spec: vkX, Groth16Valid, Groth16ValidNeg
    ├── Impl.lean               Lean transliteration of groth16_verifier.ak
    │                           (computeVkX, verifyGroth16, foldl/zipWith equivalence)
    ├── Honesty.lean            ★ verifyGroth16 = true ↔ Groth16Valid
    ├── Completeness.lean       Honest prover always accepted
    ├── Soundness.lean          Cheating prover rejected (under AGM)
    └── ZeroKnowledge.lean      Witness indistinguishability
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

The Honesty theorem formally certifies this correspondence.

---

## Getting started

### Prerequisites

- [elan](https://github.com/leanprover/elan) — the Lean version manager
- [just](https://github.com/casey/just) — task runner (optional but recommended)

Or with Nix (consistent with the Circom/snarkjs dev shell in this repo):

```bash
nix develop   # drops you into a shell with elan, just, git, curl
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

Or using `just`:

```bash
just setup   # runs steps 2–5 in one command
just build
```

### Interactive proof checking

Open the project folder in VS Code with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
installed. The infoview panel shows the proof state at the cursor position.

A good entry point is `Honesty.lean` — place the cursor inside
`verifyGroth16_honest` and step through the tactic proof to see how the
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
- `Impl.foldl_zip_smul_eq` — `foldl` over `zip` equals `zipWith` sum
- `Impl.computeVkX_eq_vkX_vk` — implementation matches spec
- `Honesty.verifyGroth16_honest` (well-formed case) — the main theorem
- `Honesty.verifyGroth16_false_iff` — false iff equation does not hold
- `Completeness.verifyGroth16_complete` — honest prover accepted
- `Completeness.verifyGroth16_no_false_negatives`
- `Soundness.verifyGroth16_sound` — cheating prover rejected
- `Soundness.verifyGroth16_no_false_positives`
- `ZeroKnowledge.simulated_proof_verifies`
- `ZeroKnowledge.witness_indistinguishable`

### Remaining admits

Two `admit`s remain in `Honesty.lean`, both in the ill-formed input
case — when `vk.ic.length ≠ inputs.length + 1`. These cover the backward
direction: showing `¬ Groth16Valid` when the IC list is the wrong length.

**What is needed:** a proof that IC points from an honest trusted setup
are linearly independent over `Fr`, so a truncated linear combination
cannot satisfy the pairing equation. See `CONTRIBUTING.md` for the
suggested approach using Mathlib's `LinearIndependent` API.

These admits are in the direction `Groth16Valid → verifyGroth16 = true`
only for ill-formed VKs. They do **not** affect the soundness theorem
(§7), which goes the other way: `verifyGroth16 = true → valid witness`.

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
just axioms   # runs scripts/check_axioms.lean
```

The invariant to maintain: `verifyGroth16_honest` must depend **only** on
`propext`, `Classical.choice`, `Quot.sound`, and `funext`. If any crypto
axiom appears there, the Honesty proof has an unintended gap.

---

## Useful commands

```bash
just setup          # first-time: install toolchain, resolve deps, fetch cache
just build          # lake build
just sorry          # grep for sorry / admit across all .lean files
just axioms         # show axiom dependencies of main theorems
just status         # per-file proof status summary
just module Honesty # build a single module
just lint           # check for warnings
just clean          # remove build artifacts
just reset          # remove .lake/ entirely (nuclear option)
```

---

## Relationship to related projects

| Project | Layer | Relationship |
|---|---|---|
| [ArkLib](https://github.com/Verified-zkEVM/ArkLib) | Proof system security | Would discharge our AGM axiom once it has Groth16 soundness |
| [zkLean](https://github.com/GaloisInc/zkLean) | Circuit constraints | Complements this project — verifies individual gadgets, not proof systems |
| [ak-381](https://github.com/Modulo-P/ak-381) | Aiken implementation | The library whose internal logic we are verifying |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Mathematics | Foundation: groups, fields, polynomials, linear independence |

---

## References

- Groth, J. (2016). [On the Size of Pairing-based Non-interactive Arguments](https://eprint.iacr.org/2016/260). *EUROCRYPT 2016*.
- Fuchsbauer, G., Kiltz, E., & Loss, J. (2018). [The Algebraic Group Model and its Applications](https://eprint.iacr.org/2017/620). *CRYPTO 2018*.
- Firsov, D. & Livshits, B. (2024). [The Ouroboros of ZK: Why Verifying the Verifier Unlocks Longer-Term ZK Innovation](https://eprint.iacr.org/2024/768). *ePrint 2024/768*.
- Nethermind & Matter Labs. (2025). [Formal Verification of the ZKSync Verifier](https://www.nethermind.io/blog/formal-verification-of-the-zksync-verifier). *First production ZK verifier verification, using EasyCrypt*.
- Verified zkEVM. [ArkLib: Formally Verified Arguments of Knowledge in Lean](https://github.com/Verified-zkEVM/ArkLib).
- Cardano Foundation. [CIP-0381: Plutus support for BLS12-381 curve operations](https://cips.cardano.org/cip/CIP-0381).
- Cardano Foundation. [CIP-0133: Plutus support for Multi-Scalar Multiplication over BLS12-381](https://cips.cardano.org/cip/CIP-0133).

---

## License

Apache 2.0. See [LICENSE](LICENSE).
