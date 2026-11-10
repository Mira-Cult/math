import PASoundness.PAtoCompactPredecessor
import PASoundness.CompactFreshen

/-! Capture-safe K renaming of the two sibling existential witness binders in
`greatestSubsetsCode`. It preserves the explicit x, u, k and order-test t labels;
no existence, arithmetic domain, induction, quotient, or soundness theorem is
asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGreatestWitnessAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactGreatestSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both existential witness binders can be changed from m to n when all
names shown are pairwise distinct. The result is an actual K derivation. -/
def greatest_witness_rename (x u k m t n : Nat)
    (fresh : [x,u,k,m,t,n].Nodup) :
    KDerivation (imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x u k n t)) := by
  have hmn : m ≠ n := by intro h; subst m; simp at fresh
  have hmu : m ≠ u := by intro h; subst m; simp at fresh
  have hmt : m ≠ t := by intro h; subst m; simp at fresh
  have hnu : n ≠ u := by intro h; subst n; simp at fresh
  have hnt : n ≠ t := by intro h; subst n; simp at fresh
  let A : Formula := .all k (.imp (.member u k) (.member x k))
  let B : Formula := .member u m
  let C : Formula := namedBoth (.member u m) (.all t (namedGreatestBody u m t))
  have h1 := ProofEquiv.alphaExists m n B hmn
    (by simp [B, Formula.binders])
    (by simp [B, Formula.names, hnu, Ne.symm hmn])
  have h2 := ProofEquiv.alphaExists m n C hmn
    (by simp [C, namedBoth, namedGreatestBody, namedEither, Formula.binders, hmt])
    (by simp [C, namedBoth, namedGreatestBody, namedEither, Formula.names,
      hnu, hnt, Ne.symm hmn])
  have h := ProofEquiv.universal u (ProofEquiv.implication (ProofEquiv.refl A)
    (ProofEquiv.implication h1 h2))
  simpa [A, B, C, namedBoth, namedGreatestBody, namedEither, greatestSubsetsCode,
    subsetCode, nonemptyCode, hasGreatestCode, greatestCode, Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    CompactDerivations.either, hmu, hmt, hmn, hnu, hnt, Ne.symm hmu, Ne.symm hmt,
    Ne.symm hmn, Ne.symm hnu, Ne.symm hnt] using h.forward

theorem greatest_witness_rename_certificate (x u k m t n : Nat)
    (fresh : [x,u,k,m,t,n].Nodup) :
    theoremCode (certificate (greatest_witness_rename x u k m t n fresh)) =
      imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x u k n t) :=
  certificate_correct (greatest_witness_rename x u k m t n fresh)

end PASoundness.PAtoCompactGreatestWitnessAlpha

#print axioms PASoundness.PAtoCompactGreatestWitnessAlpha.greatest_witness_rename
#print axioms PASoundness.PAtoCompactGreatestWitnessAlpha.greatest_witness_rename_certificate
