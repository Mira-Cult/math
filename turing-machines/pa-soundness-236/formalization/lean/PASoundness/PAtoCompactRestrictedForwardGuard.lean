import PASoundness.PAtoCompactRestrictedForwardPoint
import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19

/-! The restricted forward uniqueness guard implies the corresponding old
guard. This is literal K proof data under supplied successor and filter
premises, not a uniqueness, bijection, or quotient theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedForwardGuard
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactRestrictedForwardPoint
open PASoundness.PAtoCompactRestrictionEdgeReverseClosed PASoundness.PAtoCompactRestrictionFresh19
open PASoundness.PAtoCompactRestrictionFilterVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under supplied raw successor S(5,1) and the exact endpoint filter,
every restricted edge 7→4 to an old target member 4∈5 is also an old-graph
edge to a successor member 4∈1. Bound name 4 is fresh in both premises;
the fixed labels do not impose inequality on the denoted objects. Code 1
is literal membership of name 0 in itself. -/
def restricted_guard_to_original : KDerivation
    (imp (successorCode 5 1 10) (imp filter
      (allCode 4 (imp
        (both (member 5 4) (graphFormula 8 7 4).encode)
        (both (member 1 4) (graphFormula 6 7 4).encode))))) := by
  let S := successorCode 5 1 10
  let F := filter
  let A := both (member 5 4) (graphFormula 8 7 4).encode
  let B := both (member 1 4) (graphFormula 6 7 4).encode
  let Γ := [F,S]
  have hf19 : 19 ∉ (namedFilter 6 8 14 2 5).names :=
    filter_fresh_19 6 8 14 2 5 (by decide)
  have hpoint : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := .head _ _
    have hold : Context Δ (member 5 4) := Context.conjunctionLeft ha
    have hedge : Context Δ (graphFormula 8 7 4).encode := Context.conjunctionRight ha
    have hs : Context Δ S := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hnew : Context Δ (member 1 4) :=
      .mp (Context.disjunctionRight hold)
        (.mp hs (.closed (successor_include 5 1 10 4 (by decide) (by decide) (by decide))))
    have horig : Context Δ (graphFormula 6 7 4).encode :=
      .mp hedge (.mp hf (.closed
        (restricted_edge_source 6 8 14 2 5 7 4 (by decide) (by decide) (by decide) hf19)))
    exact Context.conjunctionIntro hnew horig
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = F
    · subst z
      simpa only [F, filter] using
        (restriction_filter_vacuity 6 8 14 2 5 4 (by decide))
    have he : z = S := by simp_all
    subst z
    exact successor_vacuity 5 1 10 4 (by decide) (by decide) (by decide)
  have hall : Context Γ (allCode 4 (imp A B)) := Context.generalize 4 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem restricted_guard_to_original_certificate :
    theoremCode (certificate restricted_guard_to_original) =
      imp (successorCode 5 1 10) (imp filter
        (allCode 4 (imp
          (both (member 5 4) (graphFormula 8 7 4).encode)
          (both (member 1 4) (graphFormula 6 7 4).encode)))) :=
  certificate_correct restricted_guard_to_original

end PASoundness.PAtoCompactRestrictedForwardGuard

#print axioms PASoundness.PAtoCompactRestrictedForwardGuard.restricted_guard_to_original
#print axioms PASoundness.PAtoCompactRestrictedForwardGuard.restricted_guard_to_original_certificate
