import PASoundness.PAtoCompactLeastCounterexample
import PASoundness.CompactFreshen

/-! Capture-safe alpha conversion of the least-witness binder in the literal
K least-subsets formula. No candidate existence, quotient, induction or
semantic soundness theorem is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateAlphaLeastWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the least-member existential binder without changing the
nonemptiness witness, subset-test binder, or order-test binder. -/
def least_witness_rename (x u k a m r n : Nat)
    (fresh : [x,u,k,a,m,r,n].Nodup) :
    KDerivation (imp (leastSubsetsCode x u k a m r) (leastSubsetsCode x u k a n r)) := by
  have hmn : m ≠ n := by intro h; subst m; simp at fresh
  have hmu : m ≠ u := by intro h; subst m; simp at fresh
  have hmr : m ≠ r := by intro h; subst m; simp at fresh
  have hnu : n ≠ u := by intro h; subst n; simp at fresh
  have hnr : n ≠ r := by intro h; subst n; simp at fresh
  let A : Formula := .all k (.imp (.member u k) (.member x k))
  let B : Formula := .ex a (.member u a)
  let C : Formula := namedLeastMember u m r
  have h1 := ProofEquiv.alphaExists m n C hmn
    (by simp [C, namedLeastMember, namedBoth, namedEither, Formula.binders, hmr])
    (by simp [C, namedLeastMember, namedBoth, namedEither, Formula.names,
      hnu, hnr, Ne.symm hmn])
  have h := ProofEquiv.universal u (ProofEquiv.implication (ProofEquiv.refl A)
    (ProofEquiv.implication (ProofEquiv.refl B) h1))
  simpa [A, B, C, namedLeastMember, namedBoth, namedEither, leastSubsetsCode,
    leastMemberCode, subsetCode, nonemptyCode, Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    CompactDerivations.either, hmu, hmr, hmn, hnu, hnr, Ne.symm hmu, Ne.symm hmr,
    Ne.symm hmn, Ne.symm hnu, Ne.symm hnr] using h.forward

theorem least_witness_rename_certificate (x u k a m r n : Nat)
    (fresh : [x,u,k,a,m,r,n].Nodup) :
    theoremCode (certificate (least_witness_rename x u k a m r n fresh)) =
      imp (leastSubsetsCode x u k a m r) (leastSubsetsCode x u k a n r) :=
  certificate_correct (least_witness_rename x u k a m r n fresh)

end PASoundness.PAtoCompactCandidateAlphaLeastWitness

#print axioms PASoundness.PAtoCompactCandidateAlphaLeastWitness.least_witness_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaLeastWitness.least_witness_rename_certificate
