import PASoundness.PAtoCompactMaximumImagePreimageElim
import PASoundness.PAtoCompactBijectionForwardImage
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity

/-! The top edge of a supplied bijective order graph between raw successors.
All graph and order hypotheses remain explicit; no quotient cancellation or
unrestricted graph construction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMaximumImageEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactMaximumImagePreimageElim PASoundness.PAtoCompactBijectionForwardImage
open PASoundness.PAtoCompactBijectionVacuity PASoundness.PAtoCompactOrderIsoVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For supplied successors S(2,0), S(5,1), transitive 5, and the exact
bijection and order clauses for graph 6, the edge 2→5 follows from the two
displayed endpoint membership guards. The forward-image witness at name 3
is obtained from the bijection and eliminated; all names are syntactic
labels, while denoted objects may coincide. Code 1 remains literal membership
of name 0 in itself. -/
def maximum_image_edge : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
        (imp orderFormula.encode (imp (member 0 2)
          (imp (member 1 5) (graphFormula 6 2 5).encode))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let T := transitiveCode 5 11 12
  let B := bijectionFormula.encode
  let O := orderFormula.encode
  let X := member 0 2
  let Y := member 1 5
  let G : Formula := graphFormula 6 2 5
  let W := both (member 1 3) (graphFormula 6 2 3).encode
  let Γ := [Y,X,O,B,T,SY,SX]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = Y
    · subst z; exact membershipVacuity 1 5 3 (by decide) (by decide)
    by_cases he : z = X
    · subst z; exact membershipVacuity 0 2 3 (by decide) (by decide)
    by_cases he : z = O
    · subst z; exact order_vacuity 3 order_fresh_3
    by_cases he : z = B
    · subst z; exact bijection_vacuity_three
    by_cases he : z = T
    · subst z; exact transitive_vacuity 5 11 12 3 (by decide) (by decide) (by decide)
    by_cases he : z = SY
    · subst z; exact successor_vacuity 5 1 10 3 (by decide) (by decide) (by decide)
    have he : z = SX := by simp_all
    subst z
    exact successor_vacuity 2 0 9 3 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp W G.encode) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hz : Context Δ (member 1 3) := Context.conjunctionLeft hw
    have hh : Context Δ (graphFormula 6 2 3).encode := Context.conjunctionRight hw
    have hsx : Context Δ SX := .hypothesis (by simp [Δ,Γ])
    have hsy : Context Δ SY := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hb : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hx : Context Δ X := .hypothesis (by simp [Δ,Γ])
    have hy : Context Δ Y := .hypothesis (by simp [Δ,Γ])
    have heq : Context Δ (equal 3 5) :=
      .mp hh (.mp hz (.mp hy (.mp hx (.mp ho (.mp hb (.mp ht
        (.mp hsy (.mp hsx (.closed maximum_image_of_edge)))))))))
    let P : Formula := graphFormula 6 2 3
    have hreplace : KDerivation (imp (equal 3 5) (imp P.encode G.encode)) := by
      have h := (CompactNamed.equalityReplace 3 5 P (by decide) (by decide)).1
      have he : CompactNamed.replace 3 5 P = G := by decide
      simpa only [he] using h
    exact .mp hh (.mp heq (.closed hreplace))
  have hex : Context Γ (existsCode 3 W) := by
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hx : Context Γ X := .hypothesis (by simp [Γ])
    exact .mp hx (.mp hb (.closed forward_image))
  have hresult : Context Γ G.encode := Context.existsElim (G.vacuity 3 (by decide))
    (Context.generalize 3 hv hlocal) hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem maximum_image_edge_certificate : theoremCode (certificate maximum_image_edge) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
        (imp orderFormula.encode (imp (member 0 2)
          (imp (member 1 5) (graphFormula 6 2 5).encode)))))) :=
  certificate_correct maximum_image_edge

end PASoundness.PAtoCompactMaximumImageEdge

#print axioms PASoundness.PAtoCompactMaximumImageEdge.maximum_image_edge
#print axioms PASoundness.PAtoCompactMaximumImageEdge.maximum_image_edge_certificate
