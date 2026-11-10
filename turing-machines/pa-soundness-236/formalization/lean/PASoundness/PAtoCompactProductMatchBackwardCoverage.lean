import PASoundness.PAtoCompactProductMatchForwardCoverage
import PASoundness.PAtoCompactProductMatchAdjoinSplit
import PASoundness.PAtoCompactTransitiveClosure

/-! Backward coverage for the inside-source product-match graph extension.
The selected path, successor, pair, point adjunction and old invariant remain
literal K antecedents; this alone is not a graph-collection proof. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchBackwardCoverage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchOutsideStep
open PASoundness.PAtoCompactProductMatchInsideImage PASoundness.PAtoCompactProductMatchForwardCoverage
open PASoundness.PAtoCompactProductMatchAdjoinSplit

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def backwardCoverage : Formula := .all 56 (.all 57
  (.imp (namedBoth (.member 2 56) (.member 44 57))
    (.imp (graphFormula 17 56 57) (namedBoth (.member 59 56) matchAt))))

/-- Every new graph edge at guarded endpoints is in the next prefix and is
an actual match: it is either inherited from the old graph or is the selected
adjoined pair. -/
def backward_all : KDerivation (imp supplied.encode backwardCoverage.encode) := by
  let U := supplied.encode
  let X := member 2 56
  let Y := member 44 57
  let Q := both X Y
  let O := matchAt.encode
  let G := (graphFormula 17 56 57).encode
  let G₀ := (graphFormula 58 56 57).encode
  let N := member 59 56
  let M := member 74 56
  let Γ := [U]
  have hlocal : Context Γ (imp Q (imp G (both N O))) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [G,Q,U]
    have hedge : Context Δ G := .head _ _
    have hguard : Context Δ Q := .hypothesis (by simp [Δ])
    have hu : Context Δ U := .hypothesis (by simp [Δ])
    have hu' : Context Δ (both selectedPath.encode (both (successorCode 74 59 76)
        (both (pairFormula 16 74 35).encode (both (adjoinCode 58 16 17 18) oldMatch.encode)))) := by
      simpa [U, supplied, namedSuccessor, successorCode, namedSuccessorBody, namedAdjoin,
        adjoinCode, namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using hu
    have hx : Context Δ X := Context.conjunctionLeft hguard
    have hy : Context Δ Y := Context.conjunctionRight hguard
    have hselected : Context Δ selectedPath.encode := Context.conjunctionLeft hu'
    have ht₁ := Context.conjunctionRight hu'
    have hs : Context Δ (successorCode 74 59 76) := Context.conjunctionLeft ht₁
    have ht₂ := Context.conjunctionRight ht₁
    have hpair : Context Δ (pairFormula 16 74 35).encode := Context.conjunctionLeft ht₂
    have ht₃ := Context.conjunctionRight ht₂
    have hadj : Context Δ (adjoinCode 58 16 17 18) := Context.conjunctionLeft ht₃
    have hold : Context Δ oldMatch.encode := Context.conjunctionRight ht₃
    have hpoint : Context Δ oldPoint.encode := .mp hold (.closed old_match_instance)
    have hpoint' : Context Δ (imp Q (both (imp G₀ (both M O))
        (imp (both M O) G₀))) := by
      simpa [oldPoint, Q, X, Y, G₀, M, O, namedBoth, Formula.not, Formula.encode, both, neg] using hpoint
    have holdback : Context Δ (imp G₀ (both M O)) :=
      Context.conjunctionLeft (.mp (Context.conjunctionIntro hx hy) hpoint')
    have hcases : Context Δ (either G₀ (both (equal 56 74) (equal 57 35))) :=
      .mp hedge (.mp hpair (.mp hadj (.closed edge_split)))
    apply Context.disjunctionElim hcases
    · let Ξ := [G₀,G,Q,U]
      have he : Context Ξ G₀ := .head _ _
      have holdpair : Context Ξ (both M O) := .mp he (.under holdback _)
      have holdmember : Context Ξ M := Context.conjunctionLeft holdpair
      have hchoice : Context Ξ (either (equal 56 74) M) := Context.disjunctionRight holdmember
      have hnext : Context Ξ N := .mp hchoice (.mp (.under hs _)
        (.closed (successor_include 74 59 76 56 (by decide) (by decide) (by decide))))
      exact Context.conjunctionIntro hnext (Context.conjunctionRight holdpair)
    · let Ξ := [both (equal 56 74) (equal 57 35),G,Q,U]
      have he : Context Ξ (both (equal 56 74) (equal 57 35)) := .head _ _
      have hsource : Context Ξ (equal 56 74) := Context.conjunctionLeft he
      have htarget : Context Ξ (equal 57 35) := Context.conjunctionRight he
      have hchoice : Context Ξ (either (equal 56 74) M) := Context.disjunctionLeft hsource
      have hnext : Context Ξ N := .mp hchoice (.mp (.under hs _)
        (.closed (successor_include 74 59 76 56 (by decide) (by decide) (by decide))))
      have hpath : Context Ξ O := .mp (.under hselected _)
        (.mp htarget (.mp hsource (.closed selected_path_at_query)))
      exact Context.conjunctionIntro hnext hpath
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
  simpa [backwardCoverage, U, Q, X, Y, N, O, G, namedBoth, Formula.not,
    Formula.encode, both, neg] using hall

theorem backward_all_certificate : theoremCode (certificate backward_all) =
    imp supplied.encode backwardCoverage.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchBackwardCoverage

#print axioms PASoundness.PAtoCompactProductMatchBackwardCoverage.backward_all
#print axioms PASoundness.PAtoCompactProductMatchBackwardCoverage.backward_all_certificate
