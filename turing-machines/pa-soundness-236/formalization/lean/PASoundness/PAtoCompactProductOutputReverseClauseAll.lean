import PASoundness.PAtoCompactProductOutputReverseClause

/-! Quantify reverse existence and uniqueness on one supplied actual output
graph. The source matrix, output bijection and actual invariant remain
explicit. Product lex order and canonical syntax alignment remain separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseClauseAll

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactProductOutputActualPoint
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputReverseClause

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverseClause : Formula := .all 33 (.imp (.member 42 33) (.ex 30 (.ex 31 reverseWitness)))

def reverse_clause_all : KDerivation (imp assumptions.encode (imp actualInvariant.encode reverseClause.encode)) := by
  let Γ := [actualInvariant.encode,assumptions.encode]
  have hi : Context Γ actualInvariant.encode := .head _ _
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hp := Context.mp hi (Context.mp ha (.closed reverse_clause_point))
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 33 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = actualInvariant.encode
    · subst q; exact free_vacuity 33 actualInvariant (by decide)
    · have he' : q = assumptions.encode := hq.resolve_left he
      subst q; exact free_vacuity 33 assumptions (by decide)
  have hall := Context.generalize 33 hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, reverseClause, CompactNamed.Formula.encode] using hall

theorem reverse_clause_all_certificate : theoremCode (certificate reverse_clause_all) =
    imp assumptions.encode (imp actualInvariant.encode reverseClause.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseClauseAll

#print axioms PASoundness.PAtoCompactProductOutputReverseClauseAll.reverse_clause_all
#print axioms PASoundness.PAtoCompactProductOutputReverseClauseAll.reverse_clause_all_certificate
