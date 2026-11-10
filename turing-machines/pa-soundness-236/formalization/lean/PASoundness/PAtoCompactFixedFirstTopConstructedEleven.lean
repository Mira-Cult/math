import PASoundness.PAtoCompactFixedFirstTopCoverageEleven
import PASoundness.PAtoCompactKuratowskiAnyNames
import PASoundness.PAtoCompactPointAdjoinSelector
import PASoundness.PAtoCompactPointAdjoin

/-! K constructs the pair and graph witnesses for a single new fixed-first
row point, given an F-edge. This is not the quantified row invariant, row
collection or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstTopConstructedEleven
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactKuratowskiAnyNames PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPointAdjoinSelector PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFixedFirstTopCoverageEleven
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def F : Formula := graphFormula 6 0 4
private def P : Formula := pairFormula 12 30 0
private def Q : Formula := pairFormula 13 12 4
private def A : Formula := namedAdjoin 7 13 11 14
private def B : Formula := namedBoth A topCoverage11

private def inner_exists : KDerivation (existsCode 12 P.encode) :=
  pair_exists_with_names 30 0 12 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private def outer_exists : KDerivation (existsCode 13 Q.encode) :=
  pair_exists_with_names 12 4 13 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private def adjoin_exists : KDerivation (existsCode 11 A.encode) := by
  have hlarge := (predicate_names_lt 7 13 17).2.2
  have h := adjoin_graph_exists_fresh 7 13 17 14 11
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by omega)
  simpa [A,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h

private def adjoined_point : KDerivation (imp A.encode (member 11 13)) := by
  let f := namedBoth (.imp (.member 11 14) (namedEither (.equal 14 13) (.member 7 14)))
    (.imp (namedEither (.equal 14 13) (.member 7 14)) (.member 11 14))
  have hi := universalInstance 14 13 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp A.encode
      (both (imp (member 11 13) (either (equal 13 13) (member 7 13)))
        (imp (either (equal 13 13) (member 7 13)) (member 11 13)))) := by
    simpa [A,f,namedAdjoin,namedBoth,namedEither,adjoinCode,Formula.encode,
      replace,rename,both,neg,either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [A.encode] A.encode := .head [] _
  have hor : Context [A.encode] (either (equal 13 13) (member 7 13)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 13))
  exact .mp hor (Context.conjunctionRight (.mp ha (.closed hi')))

private def local_step : KDerivation (imp F.encode (imp P.encode (imp Q.encode
    (imp A.encode B.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [A.encode,Q.encode,P.encode,F.encode]
  have ha : Context Γ A.encode := .head _ _
  have hq : Context Γ Q.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ P.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 11 13) := .mp ha (.closed adjoined_point)
  have hc : Context Γ topCoverage11.encode := .mp hm (.mp hq (.mp hp (.mp hf
    (.closed top_coverage11_from_witnesses))))
  exact Context.conjunctionIntro ha hc

private def graph_of_pairs : KDerivation (imp F.encode (imp P.encode (imp Q.encode
    (existsCode 11 B.encode)))) := by
  let R := namedBoth F (namedBoth P Q)
  have hstep : KDerivation (imp R.encode (imp A.encode B.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A.encode,R.encode]
    have ha : Context Γ A.encode := .head _ _
    have hr : Context Γ R.encode := .hypothesis (by simp [Γ])
    have hf := Context.conjunctionLeft hr
    have hp := Context.conjunctionLeft (Context.conjunctionRight hr)
    have hq := Context.conjunctionRight (Context.conjunctionRight hr)
    exact .mp ha (.mp hq (.mp hp (.mp hf (.closed local_step))))
  have hcong := conditionalExistsCongr 11 (R.vacuity 11 (by decide)) hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [Q.encode,P.encode,F.encode]
  have hq : Context Γ Q.encode := .head _ _
  have hp : Context Γ P.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ R.encode := Context.conjunctionIntro hf (Context.conjunctionIntro hp hq)
  exact .mp (.closed adjoin_exists) (.mp hr (.closed hcong))

private def graph_of_inner : KDerivation (imp F.encode (imp P.encode
    (existsCode 13 (both Q.encode (existsCode 11 B.encode))))) := by
  let R := namedBoth F P
  let C := namedBoth Q (.ex 11 B)
  have hstep : KDerivation (imp R.encode (imp Q.encode C.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [Q.encode,R.encode]
    have hq : Context Γ Q.encode := .head _ _
    have hr : Context Γ R.encode := .hypothesis (by simp [Γ])
    have hf := Context.conjunctionLeft hr
    have hp := Context.conjunctionRight hr
    have he : Context Γ (existsCode 11 B.encode) := .mp hq (.mp hp (.mp hf (.closed graph_of_pairs)))
    exact Context.conjunctionIntro hq he
  have hcong := conditionalExistsCongr 13 (R.vacuity 13 (by decide)) hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [P.encode,F.encode]
  have hp : Context Γ P.encode := .head _ _
  have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ R.encode := Context.conjunctionIntro hf hp
  simpa [C,namedBoth,Formula.encode,both,neg] using
    (Context.mp (.closed outer_exists) (Context.mp hr (.closed hcong)))

/-- Given an F-edge for the top index, K constructs the coordinate pair, the
nested edge and an adjoining graph, retaining the actual top-coverage body.
The old graph is the free label 7; all other witnesses have displayed scopes. -/
def top_coverage_constructed : KDerivation (imp F.encode (existsCode 12
    (both P.encode (existsCode 13 (both Q.encode (existsCode 11
      (both (adjoinCode 7 13 11 14) topCoverage11.encode))))))) := by
  let D := namedBoth P (.ex 13 (namedBoth Q (.ex 11 B)))
  have hstep : KDerivation (imp F.encode (imp P.encode D.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P.encode,F.encode]
    have hp : Context Γ P.encode := .head _ _
    have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
    have hg : Context Γ (existsCode 13 (both Q.encode (existsCode 11 B.encode))) :=
      .mp hp (.mp hf (.closed graph_of_inner))
    simpa [D,namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro hp hg
  have hcong := conditionalExistsCongr 12 (F.vacuity 12 (by decide)) hstep
  have h : KDerivation (imp F.encode (existsCode 12 D.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact .mp (.closed inner_exists) (.mp (Context.head [] _) (.closed hcong))
  simpa [D,B,A,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h

theorem top_coverage_constructed_certificate :
    theoremCode (certificate top_coverage_constructed) = imp F.encode (existsCode 12
      (both P.encode (existsCode 13 (both Q.encode (existsCode 11
        (both (adjoinCode 7 13 11 14) topCoverage11.encode)))))) :=
  certificate_correct top_coverage_constructed
end PASoundness.PAtoCompactFixedFirstTopConstructedEleven
#print axioms PASoundness.PAtoCompactFixedFirstTopConstructedEleven.top_coverage_constructed
#print axioms PASoundness.PAtoCompactFixedFirstTopConstructedEleven.top_coverage_constructed_certificate
