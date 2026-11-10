import PASoundness.PAtoCompactDiagonalGraphPremises
import PASoundness.PAtoCompactDiagonalNoGarbageAll

/-! A quantified projection of a supplied K point-adjunction graph. This is
finite syntactic K derivation data and does not construct the graph or imply
collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalAdjoinCasesAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactDiagonalGraphPremises
open PASoundness.PAtoCompactDiagonalNoGarbageAll

/-- Every member of an adjoined graph is either its point or an old member. -/
def adjoin_cases_all : KDerivation
    (imp (adjoinCode 6 8 7 10) newEntryCases) := by
  let A := adjoinCode 6 8 7 10
  let f := namedAdjoin 6 8 7 10
  have hfresh : 9 ∉ f.names := by decide
  have hv : KDerivation (imp A (allCode 9 A)) := by
    have h := f.vacuity 9 hfresh
    simpa [f, namedAdjoin, PAtoCompactZeroSuccessor.namedBoth,
      PAtoCompactZeroSuccessor.namedEither, A, adjoinCode, Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [A] A := Context.head [] A
  have he : Context [A] (imp (member 7 9) (either (equal 9 8) (member 6 9))) :=
    .mp ha (.closed adjoin_entry)
  have hg := Context.generalize 9 (by
    intro h hh
    have he : h = A := by simpa using hh
    subst h
    exact hv) he
  exact hg

theorem adjoin_cases_all_certificate :
    theoremCode (certificate adjoin_cases_all) =
      imp (adjoinCode 6 8 7 10) newEntryCases :=
  certificate_correct adjoin_cases_all

end PASoundness.PAtoCompactDiagonalAdjoinCasesAll

#print axioms PASoundness.PAtoCompactDiagonalAdjoinCasesAll.adjoin_cases_all
#print axioms PASoundness.PAtoCompactDiagonalAdjoinCasesAll.adjoin_cases_all_certificate
