import PASoundness.PAtoCompactRestrictedMatrix
import PASoundness.PAtoCompactMaximumImageEdge
import PASoundness.PAtoCompactTransitiveWitness

/-! Construct an existential restricted isomorphism matrix from an explicit
endpoint-filter existence premise. No canonical quotient alignment is
asserted; code 1 is literally `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedMatrixExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactMaximumImageEdge
open PASoundness.PAtoCompactRestrictedMatrix PASoundness.PAtoCompactRestrictedOrderPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given the explicit raw successor graphs, target transitivity, original
order/bijection clauses, and existence of an endpoint filter at name 8,
K derives existence of a graph with the full displayed restricted matrix.
The original top edge and endpoint guards are derived internally. Names
are fixed syntactic labels; denoted objects may coincide. Canonical quotient
alignment and independent filter existence are separate obligations. -/
def restricted_matrix_exists : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp orderFormula.encode
        (imp bijectionFormula.encode
          (imp (existsCode 8 filter) (existsCode 8 restrictedMatrix))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let T := transitiveCode 5 11 12
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := filter
  let M := restrictedMatrix
  let Γ := [B,O,T,SY,SX]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 8 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = B
    · subst z; exact bijectionFormula.vacuity 8 (by decide)
    by_cases he : z = O
    · subst z; exact orderFormula.vacuity 8 (by decide)
    by_cases he : z = T
    · subst z; exact transitive_vacuity 5 11 12 8 (by decide) (by decide) (by decide)
    by_cases he : z = SY
    · subst z; exact successor_vacuity 5 1 10 8 (by decide) (by decide) (by decide)
    have he : z = SX := by simp_all
    subst z
    exact successor_vacuity 2 0 9 8 (by decide) (by decide) (by decide)
  have hstep : Context Γ (imp F M) := by
    apply Context.deduction
    let Δ := F :: Γ
    have hf : Context Δ F := .head _ _
    have hb : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hy : Context Δ SY := .hypothesis (by simp [Δ,Γ])
    have hx : Context Δ SX := .hypothesis (by simp [Δ,Γ])
    have hsrc : Context Δ (member 0 2) :=
      .mp hx (.closed (successor_contains_input 2 0 9 (by decide) (by decide)))
    have hdst : Context Δ (member 1 5) :=
      .mp hy (.closed (successor_contains_input 5 1 10 (by decide) (by decide)))
    have htop : Context Δ (graphFormula 6 2 5).encode :=
      .mp hdst (.mp hsrc (.mp ho (.mp hb (.mp ht (.mp hy (.mp hx
        (.closed maximum_image_edge)))))))
    exact .mp hb (.mp htop (.mp hf (.mp ho (.mp hy (.mp hx (.closed restricted_matrix))))))
  have hall : Context Γ (allCode 8 (imp F M)) := Context.generalize 8 hv hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := existsCode 8 F :: Γ
  have hfilter : Context Δ (existsCode 8 F) := .head _ _
  exact exists_map_context (Context.under hall (existsCode 8 F)) hfilter

theorem restricted_matrix_exists_certificate : theoremCode (certificate restricted_matrix_exists) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp orderFormula.encode
        (imp bijectionFormula.encode
          (imp (existsCode 8 filter) (existsCode 8 restrictedMatrix)))))) :=
  certificate_correct restricted_matrix_exists

end PASoundness.PAtoCompactRestrictedMatrixExists

#print axioms PASoundness.PAtoCompactRestrictedMatrixExists.restricted_matrix_exists
#print axioms PASoundness.PAtoCompactRestrictedMatrixExists.restricted_matrix_exists_certificate
