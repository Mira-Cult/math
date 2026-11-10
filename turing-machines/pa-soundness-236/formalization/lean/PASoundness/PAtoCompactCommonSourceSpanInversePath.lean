import PASoundness.PAtoCompactCommonSourceSpanInduction
import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Capture-safe pointwise alignment between a common-source span path and a
restricted composition path through a supplied inverse graph. The two
inverse-correspondence implications, source endpoint membership and the two
actual graph edges remain explicit K hypotheses. This does not construct an
inverse, prove a span graph exists, or assert a span bijection or order. -/
namespace PASoundness.PAtoCompactCommonSourceSpanInversePath

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccGraphOutputLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Graph 14 maps common source 1 into image 0; graph 6 is its supplied
inverse on those endpoint domains. -/
def inversePoint : Formula := .imp (namedBoth (.member 0 2) (.member 1 4))
  (namedBoth (.imp (graphFormula 14 4 2) (graphFormula 6 2 4))
    (.imp (graphFormula 6 2 4) (graphFormula 14 4 2)))

def inverseCorrespondence : Formula := .all 2 (.all 4 inversePoint)

def spanBody : Formula := namedBoth (.member 1 4)
  (namedBoth (.member 1 4) (namedBoth (graphFormula 14 4 2) (graphFormula 7 4 3)))

def spanPath : Formula := .ex 4 spanBody

def compositeBody : Formula := namedBoth (.member 1 4)
  (namedBoth (graphFormula 6 2 4) (graphFormula 7 4 3))

def compositePath : Formula := .ex 4 compositeBody

def pathGuard : Formula := namedBoth inverseCorrespondence (.member 0 2)

private def inverse_specialize : KDerivation (imp inverseCorrespondence.encode inversePoint.encode) := by
  have h2 := allSpecialize 2 (.all 4 inversePoint) (by decide)
  have h4 := allSpecialize 4 inversePoint (by decide)
  have h := compose h2 h4
  simpa only [inverseCorrespondence, Formula.encode] using h

/-- The same common-source witness converts a span path to an inverse-graph
composition path, without any candidate hypothesis on image 0. -/
def span_to_composite : KDerivation
    (imp pathGuard.encode (imp spanPath.encode compositePath.encode)) := by
  have hpoint : KDerivation (imp pathGuard.encode (imp spanBody.encode compositePath.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [spanBody.encode,pathGuard.encode]
    have hb : Context Γ spanBody.encode := .head _ _
    have hg : Context Γ pathGuard.encode := .hypothesis (by simp [Γ])
    have hi := Context.conjunctionLeft hg
    have hp : Context Γ (member 0 2) := Context.conjunctionRight hg
    have hm : Context Γ (member 1 4) := Context.conjunctionLeft hb
    have ht := Context.conjunctionRight (Context.conjunctionRight hb)
    have hf : Context Γ (graphFormula 14 4 2).encode := Context.conjunctionLeft ht
    have hs : Context Γ (graphFormula 7 4 3).encode := Context.conjunctionRight ht
    have hpair : Context Γ (both (member 0 2) (member 1 4)) := Context.conjunctionIntro hp hm
    have hclauses : Context Γ (both (imp (graphFormula 14 4 2).encode (graphFormula 6 2 4).encode)
        (imp (graphFormula 6 2 4).encode (graphFormula 14 4 2).encode)) :=
      .mp hpair (.mp hi (.closed inverse_specialize))
    have hinv : Context Γ (graphFormula 6 2 4).encode := .mp hf (Context.conjunctionLeft hclauses)
    have hbody : Context Γ compositeBody.encode :=
      Context.conjunctionIntro hm (Context.conjunctionIntro hinv hs)
    have h := Context.mp hbody (.closed (existsIntroduce 4 compositeBody (by decide)))
    simpa only [compositePath, Formula.encode] using h
  have h := guarded_exists_left 4 pathGuard.encode spanBody.encode compositePath.encode
    (free_vacuity 4 pathGuard (by decide)) (free_vacuity 4 compositePath (by decide)) hpoint
  simpa only [spanPath, Formula.encode] using h

/-- The inverse correspondence also converts a composition path back into a
span path, preserving its original common-source witness. -/
def composite_to_span : KDerivation
    (imp pathGuard.encode (imp compositePath.encode spanPath.encode)) := by
  have hpoint : KDerivation (imp pathGuard.encode (imp compositeBody.encode spanPath.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [compositeBody.encode,pathGuard.encode]
    have hb : Context Γ compositeBody.encode := .head _ _
    have hg : Context Γ pathGuard.encode := .hypothesis (by simp [Γ])
    have hi := Context.conjunctionLeft hg
    have hp : Context Γ (member 0 2) := Context.conjunctionRight hg
    have hm : Context Γ (member 1 4) := Context.conjunctionLeft hb
    have ht := Context.conjunctionRight hb
    have hf : Context Γ (graphFormula 6 2 4).encode := Context.conjunctionLeft ht
    have hs : Context Γ (graphFormula 7 4 3).encode := Context.conjunctionRight ht
    have hpair : Context Γ (both (member 0 2) (member 1 4)) := Context.conjunctionIntro hp hm
    have hclauses : Context Γ (both (imp (graphFormula 14 4 2).encode (graphFormula 6 2 4).encode)
        (imp (graphFormula 6 2 4).encode (graphFormula 14 4 2).encode)) :=
      .mp hpair (.mp hi (.closed inverse_specialize))
    have hinv : Context Γ (graphFormula 14 4 2).encode := .mp hf (Context.conjunctionRight hclauses)
    have hbody : Context Γ spanBody.encode := Context.conjunctionIntro hm
      (Context.conjunctionIntro hm (Context.conjunctionIntro hinv hs))
    have h := Context.mp hbody (.closed (existsIntroduce 4 spanBody (by decide)))
    simpa only [spanPath, Formula.encode] using h
  have h := guarded_exists_left 4 pathGuard.encode compositeBody.encode spanPath.encode
    (free_vacuity 4 pathGuard (by decide)) (free_vacuity 4 spanPath (by decide)) hpoint
  simpa only [compositePath, Formula.encode] using h

theorem span_to_composite_certificate : theoremCode (certificate span_to_composite) =
    imp pathGuard.encode (imp spanPath.encode compositePath.encode) := certificate_correct span_to_composite

theorem composite_to_span_certificate : theoremCode (certificate composite_to_span) =
    imp pathGuard.encode (imp compositePath.encode spanPath.encode) := certificate_correct composite_to_span

end PASoundness.PAtoCompactCommonSourceSpanInversePath

#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.inversePoint
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.inverseCorrespondence
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.spanBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.spanPath
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.compositeBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.compositePath
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.pathGuard
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.span_to_composite
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.composite_to_span
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.span_to_composite_certificate
#print axioms PASoundness.PAtoCompactCommonSourceSpanInversePath.composite_to_span_certificate
