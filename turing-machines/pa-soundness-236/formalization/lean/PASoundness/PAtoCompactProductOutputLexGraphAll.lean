import PASoundness.PAtoCompactProductOutputLexGraphPoint
import PASoundness.PAtoCompactFreeVacuity

/-! Quantify the guarded lex comparison for two triples of one actual output
graph. The source product matrix, output order and actual graph invariant
remain explicit antecedents. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputLexGraphAll

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductOutputActualPoint PASoundness.PAtoCompactProductOutputLexPointOrder
open PASoundness.PAtoCompactProductOutputLexGraphPoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def endpoints : Formula := namedBoth (.member 43 30) (namedBoth (.member 44 31)
  (namedBoth (.member 43 50) (namedBoth (.member 44 51) (namedBoth (.member 42 33)
    (namedBoth (.member 42 55) (namedBoth selectedTriple otherTriple))))))
def graphOrder : Formula := .all 30 (.all 31 (.all 50 (.all 51 (.all 33 (.all 55
  (.imp endpoints targetComparison))))))

def graph_order : KDerivation (imp relocatedMatrix.encode (imp firstOrder.encode
    (imp actualInvariant.encode graphOrder.encode))) := by
  let Γ := [actualInvariant.encode,firstOrder.encode,relocatedMatrix.encode]
  have hi : Context Γ actualInvariant.encode := .head _ _
  have ho : Context Γ firstOrder.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ relocatedMatrix.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (imp endpoints.encode targetComparison.encode) := by
    apply Context.deduction
    let Δ := [endpoints.encode,actualInvariant.encode,firstOrder.encode,relocatedMatrix.encode]
    have he : Context Δ endpoints.encode := .head _ _
    have hm' : Context Δ relocatedMatrix.encode := .under hm endpoints.encode
    have ho' : Context Δ firstOrder.encode := .under ho endpoints.encode
    have hi' : Context Δ actualInvariant.encode := .under hi endpoints.encode
    have hparts : Context Δ (both relocatedMatrix.encode (both firstOrder.encode
        (both actualInvariant.encode endpoints.encode))) :=
      Context.conjunctionIntro hm' (Context.conjunctionIntro ho' (Context.conjunctionIntro hi' he))
    have hg : Context Δ graphGuard.encode := by
      simpa [graphGuard, endpoints, namedBoth, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, both, neg] using hparts
    exact .mp hg (.closed graph_point_order)
  have hv (v : Nat) (hM : v ∉ relocatedMatrix.free) (hO : v ∉ firstOrder.free)
      (hI : v ∉ actualInvariant.free) : ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = actualInvariant.encode
    · subst q; exact free_vacuity v actualInvariant hI
    · by_cases ho : q = firstOrder.encode
      · subst q; exact free_vacuity v firstOrder hO
      · have hm : q = relocatedMatrix.encode := (hq.resolve_left he).resolve_left ho
        subst q; exact free_vacuity v relocatedMatrix hM
  have hall := Context.generalize 30 (hv 30 (by decide) (by decide) (by decide))
    (Context.generalize 31 (hv 31 (by decide) (by decide) (by decide))
      (Context.generalize 50 (hv 50 (by decide) (by decide) (by decide))
        (Context.generalize 51 (hv 51 (by decide) (by decide) (by decide))
          (Context.generalize 33 (hv 33 (by decide) (by decide) (by decide))
            (Context.generalize 55 (hv 55 (by decide) (by decide) (by decide)) hp)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, graphOrder, CompactNamed.Formula.encode] using hall

theorem graph_order_certificate : theoremCode (certificate graph_order) =
    imp relocatedMatrix.encode (imp firstOrder.encode (imp actualInvariant.encode graphOrder.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputLexGraphAll

#print axioms PASoundness.PAtoCompactProductOutputLexGraphAll.graph_order
#print axioms PASoundness.PAtoCompactProductOutputLexGraphAll.graph_order_certificate
