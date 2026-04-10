-- scripts/check_axioms.lean
--
-- Introspects the axiom dependencies of each theorem in this library.
--
-- Run with:
--   lake env lean scripts/check_axioms.lean
--
-- Expected output for verifyGroth16_correct:
--   'Groth16Verifier.Properties.Correctness.verifyGroth16_correct' depends on axioms:
--   [propext, Classical.choice, Quot.sound, funext]
--
-- If any cryptographic axiom (groth16_prover_correct, agm_knowledge_extractor,
-- groth16_perfect_zk) appears under verifyGroth16_correct, the Correctness
-- proof has an unintended dependency on a cryptographic assumption.

import Groth16Verifier.Properties.ZeroKnowledge

-- ── Correctness ───────────────────────────────────────────────────────────────
-- Should depend only on: propext, Classical.choice, Quot.sound, funext

#print axioms Groth16Verifier.Properties.Correctness.verifyGroth16_correct
#print axioms Groth16Verifier.Properties.Correctness.verifyGroth16_false_iff

-- ── Completeness ──────────────────────────────────────────────────────────────
-- Should depend on: groth16_prover_correct (+ the standard Lean axioms)

#print axioms Groth16Verifier.Properties.Completeness.verifyGroth16_complete

-- ── Soundness ─────────────────────────────────────────────────────────────────
-- Should depend on: agm_knowledge_extractor (+ the standard Lean axioms)

#print axioms Groth16Verifier.Properties.Soundness.verifyGroth16_sound
#print axioms Groth16Verifier.Properties.Soundness.verifyGroth16_no_false_positives
#print axioms Groth16Verifier.Properties.Soundness.verifyGroth16_iff_satisfiable

-- ── Zero-Knowledge ────────────────────────────────────────────────────────────
-- Should depend on: groth16_perfect_zk (+ the standard Lean axioms)

#print axioms Groth16Verifier.Properties.ZeroKnowledge.simulated_proof_verifies
#print axioms Groth16Verifier.Properties.ZeroKnowledge.witness_indistinguishable
