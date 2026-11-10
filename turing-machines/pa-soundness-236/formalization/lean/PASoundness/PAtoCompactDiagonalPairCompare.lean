import PASoundness.PAtoCompactKuratowskiInjectivity

/-! Compare an arbitrary pair on object 19 with a supplied diagonal pair on
the same object. Fresh alias 27 handles the repeated coordinate name 10; this
is a K proof interface, not diagonal graph existence or quotient reflexivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalPairCompare
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactKuratowskiSyntax PASoundness.PAtoCompactKuratowskiInjectivity

/-- A common representative for (a,b) and (10,10) forces a=10 and a=b.
All listed syntax names are distinct; the interpreted values may coincide. -/
def diagonal_pair_compare (a b : Nat)
    (fresh : [19,a,b,10,27,20,21,22,23,24].Nodup) :
    KDerivation (imp (pairFormula 19 a b).encode
      (imp (pairFormula 19 10 10).encode (both (equal a 10) (equal a b)))) := by
  let F : CompactNamed.Formula := .imp (pairFormula 19 a b)
    (.imp (pairFormula 19 10 10) (namedBoth (.equal a 10) (.equal a b)))
  have h27a : 27 ≠ a := by intro h; subst a; simp at fresh
  have h27b : 27 ≠ b := by intro h; subst b; simp at fresh
  have hnames : 27 ∉ F.names := by
    simp [F, pair_formula_named, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.Formula.names, h27a, h27b]
  have hv : KDerivation (imp F.encode (allCode 27 F.encode)) := F.vacuity 27 hnames
  have hrepl : CompactNamed.replace 27 10 (pairFormula 19 10 27) = pairFormula 19 10 10 := by decide
  have ht := (CompactNamed.equalityReplace 27 10 (pairFormula 19 10 27)
    (by decide) (by decide)).2
  rw [hrepl] at ht
  have hpoint : KDerivation (imp (equal 27 10) F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [(pairFormula 19 10 10).encode,(pairFormula 19 a b).encode,equal 27 10]
    have he : Context Γ (equal 27 10) := .hypothesis (by simp [Γ])
    have h1 : Context Γ (pairFormula 19 a b).encode := .hypothesis (by simp [Γ])
    have h2 : Context Γ (pairFormula 19 10 10).encode := .hypothesis (by simp [Γ])
    have h2' : Context Γ (pairFormula 19 10 27).encode := .mp h2 (.mp he (.closed ht))
    have heqs : Context Γ (both (equal a 10) (equal b 27)) :=
      .mp h2' (.mp h1 (.closed (pair_coordinates 19 a b 10 27 fresh)))
    have ha10 : Context Γ (equal a 10) := Context.conjunctionLeft heqs
    have hb10 : Context Γ (equal b 10) := Context.eqTrans (Context.conjunctionRight heqs) he
    exact Context.conjunctionIntro ha10 (Context.eqTrans ha10 (Context.eqSymm hb10))
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize 27 hpoint)) (.closed (existsEqual 27 10))

theorem diagonal_pair_compare_certificate (a b : Nat)
    (fresh : [19,a,b,10,27,20,21,22,23,24].Nodup) :
    theoremCode (certificate (diagonal_pair_compare a b fresh)) =
      imp (pairFormula 19 a b).encode
        (imp (pairFormula 19 10 10).encode (both (equal a 10) (equal a b))) :=
  certificate_correct (diagonal_pair_compare a b fresh)

end PASoundness.PAtoCompactDiagonalPairCompare

#print axioms PASoundness.PAtoCompactDiagonalPairCompare.diagonal_pair_compare
#print axioms PASoundness.PAtoCompactDiagonalPairCompare.diagonal_pair_compare_certificate
