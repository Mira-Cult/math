import PASoundness.PAtoCompactBijectionForwardWitness
import PASoundness.PAtoCompactBijectionWitnessUnique

/-! Two codomain-guarded edges from the same input have equal outputs under
the exact represented bijection clause. This is a finite K proof construction;
the proposed graph and bijection are supplied, not constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionPointwiseUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactBijectionForwardWitness PASoundness.PAtoCompactBijectionWitnessUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def target : Formula := .imp (.member 1 3)
  (.imp (graphFormula 6 2 3) (.imp (.member 1 5)
    (.imp (graphFormula 6 2 5) (.equal 3 5))))

/-- The exact bijection formula and membership of input 2 in source 0 entail
uniqueness for the two displayed codomain-guarded graph edges. The auxiliary
forward witness at name 8 is constructed from the bijection and eliminated
using explicit K vacuity. Fixed labels are distinct from graph binders;
their denoted objects may coincide. -/
def pointwise_unique : KDerivation
    (imp bijectionFormula.encode (imp (member 0 2)
      (imp (member 1 3) (imp (graphFormula 6 2 3).encode
        (imp (member 1 5) (imp (graphFormula 6 2 5).encode (equal 3 5))))))) := by
  have hstep : KDerivation (imp witness8.encode target.encode) := by
    simpa only [witness8, witnessAtEight, target, Formula.encode] using images_equal_from_witness
  have hv : KDerivation (imp target.encode (allCode 8 target.encode)) :=
    target.vacuity 8 (by decide)
  have helim : KDerivation (imp (existsCode 8 witness8.encode) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 8 hstep))
      (Context.head [] (existsCode 8 witness8.encode))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 0 2) := .head _ _
  have hw : Context Γ (existsCode 8 witness8.encode) := .mp hm (.mp hb (.closed forward_witness))
  have ht : Context Γ target.encode := .mp hw (.closed helim)
  simpa only [target, Formula.encode] using ht

theorem pointwise_unique_certificate : theoremCode (certificate pointwise_unique) =
    imp bijectionFormula.encode (imp (member 0 2)
      (imp (member 1 3) (imp (graphFormula 6 2 3).encode
        (imp (member 1 5) (imp (graphFormula 6 2 5).encode (equal 3 5)))))) :=
  certificate_correct pointwise_unique

end PASoundness.PAtoCompactBijectionPointwiseUnique

#print axioms PASoundness.PAtoCompactBijectionPointwiseUnique.pointwise_unique
#print axioms PASoundness.PAtoCompactBijectionPointwiseUnique.pointwise_unique_certificate
