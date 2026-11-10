import PASoundness.PAtoCompactRestrictedForwardWitnessExists

/-! Quantified full forward witness for a supplied restricted graph. Literal K
negation is implication to code 1 (`member 0 0`). This does not prove reverse coverage, graph existence, or a quotient theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedForwardWitnessAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictedForwardPoint PASoundness.PAtoCompactRestrictedForwardUnique
open PASoundness.PAtoCompactRestrictedForwardWitnessExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact forward clause: every old source member has a target witness with
restricted membership, edge, and uniqueness for the same chosen output. The two raw successor
graphs, original order/bijection, exact endpoint filter, and original top
edge are explicit hypotheses. All fixed labels are syntactic; their denoted
objects may coincide. -/
def restricted_forward_witness_all : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode
          (allCode 7 (imp (member 2 7)
            (existsCode 3 restrictedWitness.encode))))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let O := orderFormula.encode
  let F := filter
  let Top := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let A := member 2 7
  let E := existsCode 3 restrictedWitness.encode
  let Γ := [B,Top,F,O,SY,SX]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = B
    · subst z; exact bijectionFormula.vacuity 7 (by decide)
    by_cases he : z = Top
    · subst z; exact (graphFormula 6 2 5).vacuity 7 (by decide)
    by_cases he : z = F
    · subst z
      simpa only [F, filter] using
        (restriction_filter_vacuity 6 8 14 2 5 7 (by decide))
    by_cases he : z = O
    · subst z; exact orderFormula.vacuity 7 (by decide)
    by_cases he : z = SY
    · subst z; exact successor_vacuity 5 1 10 7 (by decide) (by decide) (by decide)
    have he : z = SX := by simp_all
    subst z
    exact successor_vacuity 2 0 9 7 (by decide) (by decide) (by decide)
  have hpoint : Context Γ (imp A E) := by
    have hb : Context Γ B := .head _ _
    have ht : Context Γ Top := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have hy : Context Γ SY := .hypothesis (by simp [Γ])
    have hx : Context Γ SX := .hypothesis (by simp [Γ])
    exact .mp hb (.mp ht (.mp hf (.mp ho (.mp hy (.mp hx (.closed restricted_forward_witness_exists))))))
  have hall : Context Γ (allCode 7 (imp A E)) := Context.generalize 7 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem restricted_forward_witness_all_certificate :
    theoremCode (certificate restricted_forward_witness_all) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode
            (allCode 7 (imp (member 2 7)
              (existsCode 3 restrictedWitness.encode)))))))) :=
  certificate_correct restricted_forward_witness_all

end PASoundness.PAtoCompactRestrictedForwardWitnessAll

#print axioms PASoundness.PAtoCompactRestrictedForwardWitnessAll.restricted_forward_witness_all
#print axioms PASoundness.PAtoCompactRestrictedForwardWitnessAll.restricted_forward_witness_all_certificate
