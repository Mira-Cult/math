import PASoundness.PAtoCompactOpenAxiomCounterexample
import PASoundness.PAtoCompactGuardedBridge

/-! A negative diagnostic for a tempting universal-elimination interface.
When the bound source variable is unused, the substituted term's variables
need not be covered by the axiom guard. This is not a proof of PA soundness
or machine acceptance. -/
namespace PASoundness.PAtoCompactAllElimGuardCounterexample

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphTruth
open PASoundness.PAtoCompactTermRenamingSemantics
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactOpenAxiomCounterexample
open PASoundness.CompactMatrix (Environment update)

/-- The universal-elimination axiom with a falsum body and variable term.
The substituted variable occurs in the term but not in the axiom. -/
def closedAxiom : Peano.Formula :=
  (FOL.allAt 0 (.falsum : Peano.Formula)).imp
    (FOL.substAt (.falsum : Peano.Formula) 0 (.var 0))

def antichainEnvironment : Environment := fun _ => 5

/-- The concrete axiom guard is the empty conjunction. -/
theorem closed_guard_true : (guardFormula closedAxiom).Realize antichainEnvironment := by
  rw [guardFormula, guardList_realize]
  simp [closedAxiom, FOL.allAt, FOL.substAt, BoundedFormula.relabel,
    BoundedFormula.subst, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset]

/-- No value can realize the variable graph at the nonordinal HF input 5.
The output name 1 and graph base 3 are capture-safe for input name 0. -/
theorem variable_graph_no_output :
    ¬ (Formula.ex 1 (termGraph id (.var 0 : Peano.Term) 1 3)).Realize antichainEnvironment := by
  intro h
  obtain ⟨a, ha⟩ := h
  let η := update antichainEnvironment 1 a
  change (andF (domainAt 3 1) (equivAt 3 0 1)).Realize η at ha
  have hd := ((andF_realize _ _ η).mp ha).1
  have he := ((andF_realize _ _ η).mp ha).2
  obtain ⟨n, hn⟩ := (domainAt_iff 3 1 (by omega) η).mp hd
  apply five_not_equivAt_ordinal 3 0 1 n η (by decide) (by decide) (by decide) ?_ hn he
  simp [η, antichainEnvironment]

/-- The concrete guard-to-graph implication fails in standard HF. -/
theorem guard_does_not_force_variable_graph :
    (guardFormula closedAxiom).Realize antichainEnvironment ∧
      ¬ (Formula.ex 1 (termGraph id (.var 0 : Peano.Term) 1 3)).Realize antichainEnvironment :=
  ⟨closed_guard_true, variable_graph_no_output⟩

/-- Consequently the particular guard-to-totality implication has no finite
K proof. K soundness is used only for this negative diagnostic, not to build a
PA proof translation. -/
theorem no_guarded_variable_graph_proof :
    ¬ KProves (imp (guardFormula closedAxiom).encode
      (Formula.ex 1 (termGraph id (.var 0 : Peano.Term) 1 3)).encode) := by
  rintro ⟨d⟩
  have h := CompactSemantics.derivation_sound d antichainEnvironment
  rw [CompactSemantics.realize_imp, Formula.encode_realize, Formula.encode_realize] at h
  exact variable_graph_no_output (h closed_guard_true)

end PASoundness.PAtoCompactAllElimGuardCounterexample

#print axioms PASoundness.PAtoCompactAllElimGuardCounterexample.closed_guard_true
#print axioms PASoundness.PAtoCompactAllElimGuardCounterexample.variable_graph_no_output
#print axioms PASoundness.PAtoCompactAllElimGuardCounterexample.guard_does_not_force_variable_graph
#print axioms PASoundness.PAtoCompactAllElimGuardCounterexample.no_guarded_variable_graph_proof
