import PASoundness.PAtoCompactRestrictedBackwardWitness
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity

/-! The backward bijection clause for a supplied endpoint-restricted graph.
All successor, order, bijection, filter and top-edge premises remain explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBackwardBijection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactRestrictedBackwardPoint PASoundness.PAtoCompactRestrictedBackwardWitness
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactBijectionVacuity
open PASoundness.PAtoCompactOrderIsoVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- From the exact supplied two successor graphs, order and original
bijection clauses, endpoint filter and old-top edge, K derives the fully
quantified backward bijection clause for source 2, target 5 and graph 8.
For each target, the same existential preimage 7 supplies membership, the
restricted edge and its ∀4 uniqueness condition. The generalization at name
3 uses explicit K vacuity, including freshening of its bound occurrences in
the original order and bijection formulas. Code 1 is literal `member 0 0`.
This does not establish the forward clause, order preservation, filter
existence, a quotient, or a PA proof translation. -/
def backward_bijection : KDerivation
    (imp sourceSuccessor (imp targetSuccessor (imp orderFormula.encode
      (imp bijectionFormula.encode (imp restriction (imp topEdge
        (allCode 3 (imp (member 5 3) (existsCode 7 restrictedWitness.encode))))))))) := by
  let SX := sourceSuccessor
  let SY := targetSuccessor
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := restriction
  let T := topEdge
  let V := member 5 3
  let C := existsCode 7 restrictedWitness.encode
  let Γ := [T,F,B,O,SY,SX]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = T
    · subst z; exact (graphFormula 6 2 5).vacuity 3 (by decide)
    by_cases he : z = F
    · subst z; exact restriction_filter_vacuity 6 8 14 2 5 3 (by decide)
    by_cases he : z = B
    · subst z; exact bijection_vacuity_three
    by_cases he : z = O
    · subst z; exact order_vacuity 3 order_fresh_3
    by_cases he : z = SY
    · subst z; exact successor_vacuity 5 1 10 3 (by decide) (by decide) (by decide)
    have he : z = SX := by simp_all
    subst z
    exact successor_vacuity 2 0 9 3 (by decide) (by decide) (by decide)
  have hpoint : Context Γ (imp V C) := by
    have hsx : Context Γ SX := .hypothesis (by simp [Γ])
    have hsy : Context Γ SY := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have ht : Context Γ T := .head _ _
    exact .mp ht (.mp hf (.mp hb (.mp ho (.mp hsy (.mp hsx (.closed backward_witness))))))
  have hall : Context Γ (allCode 3 (imp V C)) := Context.generalize 3 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem backward_bijection_certificate : theoremCode (certificate backward_bijection) =
    imp sourceSuccessor (imp targetSuccessor (imp orderFormula.encode
      (imp bijectionFormula.encode (imp restriction (imp topEdge
        (allCode 3 (imp (member 5 3) (existsCode 7 restrictedWitness.encode)))))))) :=
  certificate_correct backward_bijection

end PASoundness.PAtoCompactRestrictedBackwardBijection

#print axioms PASoundness.PAtoCompactRestrictedBackwardBijection.backward_bijection
#print axioms PASoundness.PAtoCompactRestrictedBackwardBijection.backward_bijection_certificate
