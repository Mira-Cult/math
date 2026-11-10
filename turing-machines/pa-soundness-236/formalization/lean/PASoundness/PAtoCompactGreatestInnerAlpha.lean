import PASoundness.PAtoCompactPredecessor
import PASoundness.CompactFreshen

/-! Capture-safe K renaming of the greatest-subset order-test binder. This is
an alpha conversion only; it neither proves the greatest-subsets property nor
constructs an arithmetic interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGreatestInnerAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.PAtoCompactPredecessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the inner membership-order test `t` to `r` in the literal greatest
subset formula; all displayed names are pairwise distinct. -/
def greatest_subsets_rename_order (x u k m t r : Nat)
    (fresh : [x,u,k,m,t,r].Nodup) :
    KDerivation (imp (greatestSubsetsCode x u k m t)
      (greatestSubsetsCode x u k m r)) := by
  have htu : t ≠ u := by intro h; subst t; simp at fresh
  have htm : t ≠ m := by intro h; subst t; simp at fresh
  have htr : t ≠ r := by intro h; subst t; simp at fresh
  have hru : r ≠ u := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  let f := namedGreatestBody u m t
  have ha := ProofEquiv.alphaAll t r f htr
    (by simp [f, namedGreatestBody, namedEither, Formula.binders])
    (by simp [f, namedGreatestBody, namedEither, Formula.names, hru, hrm, Ne.symm htr])
  have hrepl : replace t r f = namedGreatestBody u m r := by
    simp [f, namedGreatestBody, namedEither, replace, rename, Ne.symm htu, Ne.symm htm]
  rw [hrepl] at ha
  let A : Formula := .member u m
  have hpair : ProofEquiv (namedBoth A (.all t f))
      (namedBoth A (.all r (namedGreatestBody u m r))) := by
    exact .implication (.implication (.refl A) (.implication ha (.refl .bottom))) (.refl .bottom)
  have hw := ProofEquiv.existential m hpair
  let S : Formula := .all k (.imp (.member u k) (.member x k))
  let N : Formula := .ex m (.member u m)
  have hbody := ProofEquiv.implication (.refl S) (ProofEquiv.implication (.refl N) hw)
  have hout := ProofEquiv.universal u hbody
  simpa [S, N, A, f, namedGreatestBody, namedBoth, namedEither, Formula.encode,
    greatestSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode, greatestCode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using hout.forward

theorem greatest_subsets_rename_order_certificate (x u k m t r : Nat)
    (fresh : [x,u,k,m,t,r].Nodup) :
    theoremCode (certificate (greatest_subsets_rename_order x u k m t r fresh)) =
      imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x u k m r) :=
  certificate_correct (greatest_subsets_rename_order x u k m t r fresh)

end PASoundness.PAtoCompactGreatestInnerAlpha

#print axioms PASoundness.PAtoCompactGreatestInnerAlpha.greatest_subsets_rename_order
#print axioms PASoundness.PAtoCompactGreatestInnerAlpha.greatest_subsets_rename_order_certificate
