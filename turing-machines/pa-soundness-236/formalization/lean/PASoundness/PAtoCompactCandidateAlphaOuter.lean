import PASoundness.PAtoCompactTransitiveDomain
import PASoundness.PAtoCompactPredecessor

/-! Capture-safe K alpha conversions of the outer binders in the candidate's
member-transitivity and greatest-subset formulas. No domain, induction or
equality quotient is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateAlphaOuter
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactGreatestSuccessor

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the outer member test of the member-transitivity formula. -/
def members_transitive_rename (x b p q v : Nat) (fresh : [x,b,p,q,v].Nodup) :
    KDerivation (imp (membersTransitiveCode x b p q) (membersTransitiveCode x v p q)) := by
  have hbx : b ≠ x := by intro h; subst b; simp at fresh
  have hbv : b ≠ v := by intro h; subst b; simp at fresh
  have hbp : b ≠ p := by intro h; subst b; simp at fresh
  have hbq : b ≠ q := by intro h; subst b; simp at fresh
  have hvx : v ≠ x := by intro h; subst v; simp at fresh
  have hvp : v ≠ p := by intro h; subst v; simp at fresh
  have hvq : v ≠ q := by intro h; subst v; simp at fresh
  let f : CompactNamed.Formula := .imp (.member x b) (namedTransitive b p q)
  have h := CompactNamed.universalAlpha b v f hbv
    (by simp [f, namedTransitive, transitiveBody, CompactNamed.Formula.binders, hbp, hbq])
    (by simp [f, namedTransitive, transitiveBody, CompactNamed.Formula.names, hvx, hvp, hvq,
      Ne.symm hbv])
  simpa [f, membersTransitiveCode, namedTransitive, transitiveBody, transitiveCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    hbx, hbv, hbp, hbq, hvx, hvp, hvq, Ne.symm hbx, Ne.symm hbv,
    Ne.symm hbp, Ne.symm hbq, Ne.symm hvx, Ne.symm hvp, Ne.symm hvq] using h.1

/-- Rename the outer represented-subset binder in the greatest-subset formula. -/
def greatest_subsets_rename_outer (x u k m t v : Nat) (fresh : [x,u,k,m,t,v].Nodup) :
    KDerivation (imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x v k m t)) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have huv : u ≠ v := by intro h; subst u; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hut : u ≠ t := by intro h; subst u; simp at fresh
  have hvx : v ≠ x := by intro h; subst v; simp at fresh
  have hvk : v ≠ k := by intro h; subst v; simp at fresh
  have hvm : v ≠ m := by intro h; subst v; simp at fresh
  have hvt : v ≠ t := by intro h; subst v; simp at fresh
  let f := namedGreatestSubsetsBody x u k m t
  have h := CompactNamed.universalAlpha u v f huv
    (by simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.binders, huk, hum, hut])
    (by simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.names, hvx, hvk, hvm, hvt, Ne.symm huv])
  simpa [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
    greatestSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode, greatestCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hux, huv, huk, hum, hut, hvx, hvk, hvm, hvt,
    Ne.symm hux, Ne.symm huv, Ne.symm huk, Ne.symm hum, Ne.symm hut,
    Ne.symm hvx, Ne.symm hvk, Ne.symm hvm, Ne.symm hvt] using h.1

theorem members_transitive_rename_certificate (x b p q v : Nat) (fresh : [x,b,p,q,v].Nodup) :
    theoremCode (certificate (members_transitive_rename x b p q v fresh)) =
      imp (membersTransitiveCode x b p q) (membersTransitiveCode x v p q) :=
  certificate_correct (members_transitive_rename x b p q v fresh)

theorem greatest_subsets_rename_outer_certificate (x u k m t v : Nat)
    (fresh : [x,u,k,m,t,v].Nodup) :
    theoremCode (certificate (greatest_subsets_rename_outer x u k m t v fresh)) =
      imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x v k m t) :=
  certificate_correct (greatest_subsets_rename_outer x u k m t v fresh)

end PASoundness.PAtoCompactCandidateAlphaOuter

#print axioms PASoundness.PAtoCompactCandidateAlphaOuter.members_transitive_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaOuter.greatest_subsets_rename_outer
#print axioms PASoundness.PAtoCompactCandidateAlphaOuter.members_transitive_rename_certificate
#print axioms PASoundness.PAtoCompactCandidateAlphaOuter.greatest_subsets_rename_outer_certificate
