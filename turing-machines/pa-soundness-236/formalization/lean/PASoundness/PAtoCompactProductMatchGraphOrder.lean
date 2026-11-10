import PASoundness.PAtoCompactProductMatchPathOrder
import PASoundness.PAtoCompactProductMatchCollectionCandidate

/-! The quantified order clause for a supplied represented product-match
graph satisfying the explicit guarded invariant. Product matrices, factor
orders, first factor bijection and the invariant remain object-level
antecedents; this module does not establish bijectivity or congruence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchGraphOrder

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchRelation
open PASoundness.PAtoCompactProductMatchPathOrderPoint PASoundness.PAtoCompactProductMatchPathOrder
open PASoundness.PAtoCompactProductIsoPointwiseLex

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def actualMatch : Formula := replace 59 2 partialMatch
def matchPoint : Formula := .imp (namedBoth (.member 2 56) (.member 44 57))
  (namedBoth (.imp (graphFormula 58 56 57) (namedBoth (.member 2 56) matchAt))
    (.imp (namedBoth (.member 2 56) matchAt) (graphFormula 58 56 57)))

theorem actual_match_shape : actualMatch = .all 56 (.all 57 matchPoint) := by decide

def firstPoint : Formula := replace 57 35 (replace 56 32 matchPoint)
def secondPoint : Formula := replace 57 55 (replace 56 52 matchPoint)

/-- Both exact graph-invariant query instances, with different endpoint names. -/
def first_instance : KDerivation (imp actualMatch.encode firstPoint.encode) := by
  have h56 := universalInstance 56 32 (.all 57 matchPoint) (by decide) (by decide) (by decide)
  have hs56 : replace 56 32 (.all 57 matchPoint) = .all 57 (replace 56 32 matchPoint) := by decide
  rw [hs56] at h56
  have h57 := universalInstance 57 35 (replace 56 32 matchPoint) (by decide) (by decide) (by decide)
  rw [actual_match_shape]
  simpa [firstPoint, Formula.encode] using compose h56 h57

def second_instance : KDerivation (imp actualMatch.encode secondPoint.encode) := by
  have h56 := universalInstance 56 52 (.all 57 matchPoint) (by decide) (by decide) (by decide)
  have hs56 : replace 56 52 (.all 57 matchPoint) = .all 57 (replace 56 52 matchPoint) := by decide
  rw [hs56] at h56
  have h57 := universalInstance 57 55 (replace 56 52 matchPoint) (by decide) (by decide) (by decide)
  rw [actual_match_shape]
  simpa [secondPoint, Formula.encode] using compose h56 h57

def endpointGuard : Formula := namedBoth (.member 2 32) (namedBoth (.member 2 52)
  (namedBoth (.member 44 35) (namedBoth (.member 44 55)
    (namedBoth (graphFormula 58 32 35) (graphFormula 58 52 55)))))
def result : Formula := namedBoth (.imp (.member 52 32) (.member 55 35))
  (.imp (.member 55 35) (.member 52 32))
def outputPoint : Formula := .imp endpointGuard result
def outputOrder : Formula := .all 32 (.all 52 (.all 35 (.all 55 outputPoint)))
def matrices : Formula := namedBoth productMatrix (namedBoth targetMatrix
  (namedBoth firstBijection (namedBoth firstOrder secondOrder)))

theorem first_shape : firstPoint = .imp (namedBoth (.member 2 32) (.member 44 35))
    (namedBoth (.imp (graphFormula 58 32 35) (namedBoth (.member 2 32) path))
      (.imp (namedBoth (.member 2 32) path) (graphFormula 58 32 35))) := by decide

theorem second_shape : secondPoint = .imp (namedBoth (.member 2 52) (.member 44 55))
    (namedBoth (.imp (graphFormula 58 52 55) (namedBoth (.member 2 52) otherInput))
      (.imp (namedBoth (.member 2 52) otherInput) (graphFormula 58 52 55))) := by decide

/-- The explicit guarded graph invariant and the relevant input matrices
yield the full four-quantifier order clause on source/target members. -/
def graph_order : KDerivation (imp matrices.encode (imp actualMatch.encode outputOrder.encode)) := by
  let H := matrices.encode
  let A := actualMatch.encode
  let Γ := [A,H]
  have hlocal : Context Γ outputPoint.encode := by
    apply Context.deduction
    let Δ := [endpointGuard.encode,A,H]
    have he : Context Δ endpointGuard.encode := .head _ _
    have ha : Context Δ A := .hypothesis (by simp [Δ])
    have hm : Context Δ H := .hypothesis (by simp [Δ])
    have he' : Context Δ (both (member 2 32) (both (member 2 52)
        (both (member 44 35) (both (member 44 55)
          (both (graphFormula 58 32 35).encode (graphFormula 58 52 55).encode))))) := by
      simpa [endpointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using he
    have hm' : Context Δ (both productMatrix.encode (both targetMatrix.encode
        (both firstBijection.encode (both firstOrder.encode secondOrder.encode)))) := by
      simpa [H, matrices, namedBoth, Formula.not, Formula.encode, both, neg] using hm
    have hs₁ := Context.conjunctionLeft he'
    have hs₂ := Context.conjunctionLeft (Context.conjunctionRight he')
    have ht₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight he'))
    have ht₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he')))
    have he₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he'))))
    have he₂ := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he'))))
    have hfirst := Context.mp ha (.closed first_instance)
    have hfirst' : Context Δ (imp (both (member 2 32) (member 44 35))
        (both (imp (graphFormula 58 32 35).encode (both (member 2 32) path.encode))
          (imp (both (member 2 32) path.encode) (graphFormula 58 32 35).encode))) := by
      simpa [first_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hfirst
    have hp₁ := Context.conjunctionRight (Context.mp he₁
      (Context.conjunctionLeft (Context.mp (Context.conjunctionIntro hs₁ ht₁) hfirst')))
    have hsecond := Context.mp ha (.closed second_instance)
    have hsecond' : Context Δ (imp (both (member 2 52) (member 44 55))
        (both (imp (graphFormula 58 52 55).encode (both (member 2 52) otherInput.encode))
          (imp (both (member 2 52) otherInput.encode) (graphFormula 58 52 55).encode))) := by
      simpa [second_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hsecond
    have hp₂ := Context.conjunctionRight (Context.mp he₂
      (Context.conjunctionLeft (Context.mp (Context.conjunctionIntro hs₂ ht₂) hsecond')))
    have hpm := Context.conjunctionLeft hm'
    have htm := Context.conjunctionLeft (Context.conjunctionRight hm')
    have hb := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hm'))
    have ho₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hm')))
    have ho₂ := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hm')))
    have hg : Context Δ PASoundness.PAtoCompactProductMatchPathOrderPoint.guard.encode := by
      have h := Context.conjunctionIntro hpm (Context.conjunctionIntro htm (Context.conjunctionIntro hb
        (Context.conjunctionIntro ho₁ (Context.conjunctionIntro ho₂ (Context.conjunctionIntro hs₁ hs₂)))))
      simpa [PASoundness.PAtoCompactProductMatchPathOrderPoint.guard,
        namedBoth, Formula.not, Formula.encode, both, neg] using h
    have h := Context.mp hp₂ (Context.mp hp₁ (Context.mp hg (.closed path_order)))
    simpa [result, iffCode, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hv (v : Nat) (hvH : v ∉ matrices.names) (hvA : v ∉ actualMatch.names) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = A
    · subst q; exact actualMatch.vacuity v hvA
    · have he' : q = H := hq.resolve_left he
      subst q; exact matrices.vacuity v hvH
  have hall := Context.generalize 32 (hv 32 (by decide) (by decide))
    (Context.generalize 52 (hv 52 (by decide) (by decide))
      (Context.generalize 35 (hv 35 (by decide) (by decide))
        (Context.generalize 55 (hv 55 (by decide) (by decide)) hlocal)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, outputOrder, outputPoint, Formula.encode] using hall

theorem graph_order_certificate : theoremCode (certificate graph_order) =
    imp matrices.encode (imp actualMatch.encode outputOrder.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchGraphOrder

#print axioms PASoundness.PAtoCompactProductMatchGraphOrder.first_instance
#print axioms PASoundness.PAtoCompactProductMatchGraphOrder.second_instance
#print axioms PASoundness.PAtoCompactProductMatchGraphOrder.graph_order
#print axioms PASoundness.PAtoCompactProductMatchGraphOrder.graph_order_certificate
