import PASoundness.PAtoCompactProductMatchEndpointEdge
import PASoundness.PAtoCompactProductMatchAdjoinEdge
import PASoundness.PAtoCompactProductMatchOutsideStep
import PASoundness.PAtoCompactGraphAdjoinPreserve
import PASoundness.PAtoCompactSuccessorInjective

/-! The forward coverage direction for one inside-source product-match
graph extension. The selected path, successor, pair, point adjunction and old
graph invariant are literal antecedents. This is not the backward direction,
the full inside step, or an unconditional graph-collection theorem. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchForwardCoverage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactGraphAdjoinPreserve PASoundness.PAtoCompactProductMatchPartialBase
open PASoundness.PAtoCompactProductMatchOutsideStep PASoundness.PAtoCompactProductMatchInsideImage
open PASoundness.PAtoCompactProductMatchEndpointEdge PASoundness.PAtoCompactProductMatchAdjoinEdge

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def supplied : Formula := namedBoth selectedPath (namedBoth (namedSuccessor 74 59 76)
  (namedBoth (pairFormula 16 74 35) (namedBoth (namedAdjoin 58 16 17 18) oldMatch)))

def forwardCoverage : Formula := .all 56 (.all 57
  (.imp (namedBoth (.member 2 56) (.member 44 57))
    (.imp (namedBoth (.member 59 56) matchAt) (graphFormula 17 56 57))))

/-- Every matching query in the successor prefix is represented by the new
graph, using the original graph for old-prefix members and the selected edge
plus path functionality for the newly adjoined endpoint. -/
def forward_all : KDerivation (imp supplied.encode forwardCoverage.encode) := by
  let U := supplied.encode
  let X := member 2 56
  let Y := member 44 57
  let Q := both X Y
  let O := matchAt.encode
  let G := (graphFormula 17 56 57).encode
  let N := member 59 56
  let M := member 74 56
  let Γ := [U]
  have hlocal : Context Γ (imp Q (imp (both N O) G)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [both N O,Q,U]
    have hnew : Context Δ (both N O) := .head _ _
    have hguard : Context Δ Q := .hypothesis (by simp [Δ])
    have hu : Context Δ U := .hypothesis (by simp [Δ])
    have hu' : Context Δ (both selectedPath.encode (both (successorCode 74 59 76)
        (both (pairFormula 16 74 35).encode (both (adjoinCode 58 16 17 18) oldMatch.encode)))) := by
      simpa [U, supplied, namedSuccessor, successorCode, namedSuccessorBody, namedAdjoin,
        adjoinCode, namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using hu
    have hx : Context Δ X := Context.conjunctionLeft hguard
    have hy : Context Δ Y := Context.conjunctionRight hguard
    have hn : Context Δ N := Context.conjunctionLeft hnew
    have ho : Context Δ O := Context.conjunctionRight hnew
    have hselected : Context Δ selectedPath.encode := Context.conjunctionLeft hu'
    have ht₁ := Context.conjunctionRight hu'
    have hs : Context Δ (successorCode 74 59 76) := Context.conjunctionLeft ht₁
    have ht₂ := Context.conjunctionRight ht₁
    have hpair : Context Δ (pairFormula 16 74 35).encode := Context.conjunctionLeft ht₂
    have ht₃ := Context.conjunctionRight ht₂
    have hadj : Context Δ (adjoinCode 58 16 17 18) := Context.conjunctionLeft ht₃
    have hold : Context Δ oldMatch.encode := Context.conjunctionRight ht₃
    have hpoint : Context Δ oldPoint.encode := .mp hold (.closed old_match_instance)
    have hpoint' : Context Δ (imp Q (both
        (imp (graphFormula 58 56 57).encode (both M O))
        (imp (both M O) (graphFormula 58 56 57).encode))) := by
      simpa [oldPoint, Q, X, Y, M, O, namedBoth, Formula.not, Formula.encode, both, neg] using hpoint
    have holdcov : Context Δ (imp (both M O) (graphFormula 58 56 57).encode) :=
      Context.conjunctionRight (.mp (Context.conjunctionIntro hx hy) hpoint')
    have hedge : Context Δ (graphFormula 17 74 35).encode := .mp hpair (.mp hadj (.closed selected_edge))
    have hcases : Context Δ (either (equal 56 74) M) :=
      .mp hn (.mp hs (.closed (successor_inspect 74 59 76 56 (by decide) (by decide) (by decide))))
    apply Context.disjunctionElim hcases
    · let Ξ := [equal 56 74,both N O,Q,U]
      have he : Context Ξ (equal 56 74) := .head _ _
      exact .mp (.under ho _) (.mp (.under hedge _) (.mp (.under hselected _) (.mp he (.closed endpoint_edge))))
    · let Ξ := [M,both N O,Q,U]
      have hm : Context Ξ M := .head _ _
      have hmo : Context Ξ (both M O) := Context.conjunctionIntro hm (.under ho _)
      have holdedge : Context Ξ (graphFormula 58 56 57).encode := .mp hmo (.under holdcov _)
      exact .mp holdedge (.mp (.under hadj _) (.closed (adjoin_preserves_edge 58 16 17 18 56 57
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
  have hv56 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 56 q)) := by
    intro q hq
    have he : q = U := by simpa [Γ] using hq
    subst q
    exact free_vacuity 56 supplied (by decide)
  have hv57 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 57 q)) := by
    intro q hq
    have he : q = U := by simpa [Γ] using hq
    subst q
    exact free_vacuity 57 supplied (by decide)
  have hall := Context.generalize 56 hv56 (Context.generalize 57 hv57 hlocal)
  apply Context.closeEmpty
  apply Context.deduction
  simpa [forwardCoverage, U, Q, X, Y, N, O, G, namedBoth, Formula.not,
    Formula.encode, both, neg] using hall

theorem forward_all_certificate : theoremCode (certificate forward_all) =
    imp supplied.encode forwardCoverage.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchForwardCoverage

#print axioms PASoundness.PAtoCompactProductMatchForwardCoverage.forward_all
#print axioms PASoundness.PAtoCompactProductMatchForwardCoverage.forward_all_certificate
