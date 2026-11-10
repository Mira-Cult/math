import PASoundness.PAtoCompactProductOutputForwardClause

/-! Quantify the guarded forward product clause on one supplied actual graph.
The source product matrix, output bijection and actual graph invariant remain
literal antecedents. Reverse coverage and product order are separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputForwardClauseAll

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactProductOutputActualPoint
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputForwardClause

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def forwardClause : Formula := .all 30 (.all 31 (.imp (.member 43 30)
  (.imp (.member 44 31) (.ex 33 forwardWitness))))

def forward_clause_all : KDerivation (imp assumptions.encode (imp actualInvariant.encode forwardClause.encode)) := by
  let Γ := [actualInvariant.encode,assumptions.encode]
  have hi : Context Γ actualInvariant.encode := .head _ _
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hp := Context.mp hi (Context.mp ha (.closed forward_clause_point))
  have hv (v : Nat) (hA : v ∉ assumptions.free) (hI : v ∉ actualInvariant.free) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = actualInvariant.encode
    · subst q; exact free_vacuity v actualInvariant hI
    · have he' : q = assumptions.encode := hq.resolve_left he
      subst q; exact free_vacuity v assumptions hA
  have hall := Context.generalize 30 (hv 30 (by decide) (by decide))
    (Context.generalize 31 (hv 31 (by decide) (by decide)) hp)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, forwardClause, CompactNamed.Formula.encode] using hall

theorem forward_clause_all_certificate : theoremCode (certificate forward_clause_all) =
    imp assumptions.encode (imp actualInvariant.encode forwardClause.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputForwardClauseAll

#print axioms PASoundness.PAtoCompactProductOutputForwardClauseAll.forward_clause_all
#print axioms PASoundness.PAtoCompactProductOutputForwardClauseAll.forward_clause_all_certificate
