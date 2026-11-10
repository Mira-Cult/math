import PASoundness.PAtoCompactRestrictedForwardPoint
import PASoundness.PAtoCompactBijectionForwardAtSeven
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactTransitiveWitness

/-! One existential forward image for a supplied restricted graph. The
graph, filter and isomorphism clauses remain hypotheses; code 1 is literal
`member 0 0`. No universal totality or quotient claim is made here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedForwardExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactBijectionForwardAtSeven PASoundness.PAtoCompactBijectionVacuity
open PASoundness.PAtoCompactOrderIsoVacuity PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictedForwardPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- With raw successors S(2,0), S(5,1), a supplied original bijection and
order clause, the exact restricted filter, a supplied top edge 2→5, and old
input 7∈2, K constructs a target 3∈5 with restricted edge 7→3. The
existential output name is 3; all displayed labels are syntactic and their
denoted objects may coincide. -/
def restricted_forward_exists : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode (imp (member 2 7)
          (existsCode 3 (both (member 5 3) (graphFormula 8 7 3).encode))))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let O := orderFormula.encode
  let F := filter
  let Top := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let L := member 2 7
  let W := imageAtSeven.encode
  let H := both (member 5 3) (graphFormula 8 7 3).encode
  let Γ := [L,B,Top,F,O,SY,SX]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = L
    · subst z; exact membershipVacuity 2 7 3 (by decide) (by decide)
    by_cases he : z = B
    · subst z; exact bijection_vacuity_three
    by_cases he : z = Top
    · subst z; exact (graphFormula 6 2 5).vacuity 3 (by decide)
    by_cases he : z = F
    · subst z
      simpa only [F, filter] using
        (restriction_filter_vacuity 6 8 14 2 5 3 (by decide))
    by_cases he : z = O
    · subst z; exact order_vacuity 3 order_fresh_3
    by_cases he : z = SY
    · subst z; exact successor_vacuity 5 1 10 3 (by decide) (by decide) (by decide)
    have he : z = SX := by simp_all
    subst z
    exact successor_vacuity 2 0 9 3 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp W H) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hm : Context Δ (member 1 3) := Context.conjunctionLeft hw
    have hg : Context Δ (graphFormula 6 7 3).encode := Context.conjunctionRight hw
    have hsx : Context Δ SX := .hypothesis (by simp [Δ,Γ])
    have hsy : Context Δ SY := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ Top := .hypothesis (by simp [Δ,Γ])
    have hl : Context Δ L := .hypothesis (by simp [Δ,Γ])
    exact .mp hg (.mp hm (.mp hl (.mp ht (.mp hf (.mp ho (.mp hsy
      (.mp hsx (.closed forward_old_point))))))))
  have hex : Context Γ (existsCode 3 W) := by
    have hsx : Context Γ SX := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hl : Context Γ L := .head _ _
    have hi : Context Γ (member 0 7) := .mp (Context.disjunctionRight hl)
      (.mp hsx (.closed (successor_include 2 0 9 7 (by decide) (by decide) (by decide))))
    exact .mp hi (.mp hb (.closed forward_image_at_seven))
  have hresult : Context Γ (existsCode 3 H) :=
    exists_map_context (Context.generalize 3 hv hlocal) hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem restricted_forward_exists_certificate :
    theoremCode (certificate restricted_forward_exists) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode (imp (member 2 7)
            (existsCode 3 (both (member 5 3) (graphFormula 8 7 3).encode)))))))) :=
  certificate_correct restricted_forward_exists

end PASoundness.PAtoCompactRestrictedForwardExists

#print axioms PASoundness.PAtoCompactRestrictedForwardExists.restricted_forward_exists
#print axioms PASoundness.PAtoCompactRestrictedForwardExists.restricted_forward_exists_certificate
