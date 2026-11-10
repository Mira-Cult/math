import PASoundness.PAtoCompactProductMatchReversePathUnique
import PASoundness.PAtoCompactProductMatchReverseGraphCoverage

/-! Guarded reverse uniqueness for a supplied represented product-match graph.
The product matrices, factor bijections and exact match invariant remain inputs. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchGraphReverseUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchRelation
open PASoundness.PAtoCompactProductMatchPathOrder PASoundness.PAtoCompactProductMatchGraphOrder
open PASoundness.PAtoCompactProductMatchReverseGraphCoverage PASoundness.PAtoCompactProductMatchReversePathUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def matrices : Formula := namedBoth productMatrix (namedBoth targetMatrix
  (namedBoth firstBijection secondBijection))
def endpointGuard : Formula := namedBoth (.member 2 32) (namedBoth (.member 2 52)
  (namedBoth (.member 44 55) (namedBoth (graphFormula 58 32 55) (graphFormula 58 52 55))))
def outputPoint : Formula := .imp endpointGuard (.equal 32 52)
def reverseUniqueAll : Formula := .all 32 (.all 52 (.all 55 outputPoint))

def reverse_graph_unique : KDerivation (imp matrices.encode (imp actualMatch.encode reverseUniqueAll.encode)) := by
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
        (both (member 44 55) (both (graphFormula 58 32 55).encode (graphFormula 58 52 55).encode)))) := by
      simpa [endpointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using he
    have hm' : Context Δ (both productMatrix.encode (both targetMatrix.encode
        (both firstBijection.encode secondBijection.encode))) := by
      simpa [H, matrices, namedBoth, Formula.not, Formula.encode, both, neg] using hm
    have hx := Context.conjunctionLeft he'
    have hy := Context.conjunctionLeft (Context.conjunctionRight he')
    have hz := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight he'))
    have he₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he')))
    have he₂ := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he')))
    have hfirst := Context.mp ha (.closed query_instance)
    have hfirst' : Context Δ (imp (both (member 2 32) (member 44 55))
        (both (imp (graphFormula 58 32 55).encode (both (member 2 32) firstInput.encode))
          (imp (both (member 2 32) firstInput.encode) (graphFormula 58 32 55).encode))) := by
      simpa [query_shape, firstInput, namedBoth, Formula.not, Formula.encode, both, neg] using hfirst
    have hp₁ := Context.conjunctionRight (Context.mp he₁
      (Context.conjunctionLeft (Context.mp (Context.conjunctionIntro hx hz) hfirst')))
    have hsecond := Context.mp ha (.closed second_instance)
    have hsecond' : Context Δ (imp (both (member 2 52) (member 44 55))
        (both (imp (graphFormula 58 52 55).encode (both (member 2 52) otherInput.encode))
          (imp (both (member 2 52) otherInput.encode) (graphFormula 58 52 55).encode))) := by
      simpa [second_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hsecond
    have hp₂ := Context.conjunctionRight (Context.mp he₂
      (Context.conjunctionLeft (Context.mp (Context.conjunctionIntro hy hz) hsecond')))
    have hp := Context.conjunctionLeft hm'
    have ht := Context.conjunctionLeft (Context.conjunctionRight hm')
    have hb₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hm'))
    have hb₂ := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hm'))
    have hg : Context Δ PASoundness.PAtoCompactProductMatchReversePointUnique.assumptions.encode := by
      have h := Context.conjunctionIntro hp (Context.conjunctionIntro ht (Context.conjunctionIntro hb₁
        (Context.conjunctionIntro hb₂ (Context.conjunctionIntro hx (Context.conjunctionIntro hy hz)))))
      simpa [PASoundness.PAtoCompactProductMatchReversePointUnique.assumptions,
        namedBoth, Formula.not, Formula.encode, both, neg] using h
    simpa [Δ, outputPoint, Formula.encode] using Context.mp hp₂ (Context.mp hp₁
      (Context.mp hg (.closed reverse_path_unique)))
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
      (Context.generalize 55 (hv 55 (by decide) (by decide)) hlocal))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, reverseUniqueAll, outputPoint, Formula.encode] using hall

theorem reverse_graph_unique_certificate : theoremCode (certificate reverse_graph_unique) =
    imp matrices.encode (imp actualMatch.encode reverseUniqueAll.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchGraphReverseUnique

#print axioms PASoundness.PAtoCompactProductMatchGraphReverseUnique.reverse_graph_unique
#print axioms PASoundness.PAtoCompactProductMatchGraphReverseUnique.reverse_graph_unique_certificate
