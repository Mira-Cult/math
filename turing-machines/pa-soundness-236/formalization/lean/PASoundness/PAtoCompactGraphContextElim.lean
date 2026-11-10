import PASoundness.PAtoCompactGraphWitnessRules

/-! A graph-witness elimination rule in an explicit finite K context. The
witness label must be vacuous in the conclusion and each retained assumption;
these are supplied finite proof-data hypotheses, not semantic assumptions. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGraphContextElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGraphWitnessRules
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Expose the exact graph's pair witness under a fixed finite context, then
eliminate it. The caller supplies K vacuity for label 19 in the target and
every retained contextual formula. -/
def graph_context_elim (Γ : List Nat) (g u v : Nat) (target : Formula)
    (contextVacuity : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)))
    (targetVacuity : KDerivation (imp target.encode (allCode 19 target.encode)))
    (step : Context Γ (imp (both (member g 19) (pairFormula 19 u v).encode) target.encode))
    (graph : Context Γ (graphFormula g u v).encode) : Context Γ target.encode := by
  have hs : Context Γ (imp (graphBody g u v).encode target.encode) := by
    simpa only [graph_body_code] using step
  have hg : Context Γ (existsCode 19 (graphBody g u v).encode) := by
    simpa only [graph_code] using graph
  exact Context.existsElim targetVacuity (Context.generalize 19 contextVacuity hs) hg

/-- Retain the graph as a separate implication antecedent, so witness-label
vacuity is required only for Γ and the conclusion, not for the graph itself. -/
def graph_context_imp (Γ : List Nat) (g u v : Nat) (target : Formula)
    (contextVacuity : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)))
    (targetVacuity : KDerivation (imp target.encode (allCode 19 target.encode)))
    (step : Context Γ (imp (both (member g 19) (pairFormula 19 u v).encode) target.encode)) :
    Context Γ (imp (graphFormula g u v).encode target.encode) := by
  have hs : Context Γ (imp (graphBody g u v).encode target.encode) := by
    simpa only [graph_body_code] using step
  have hall : Context Γ (allCode 19 (imp (graphBody g u v).encode target.encode)) :=
    Context.generalize 19 contextVacuity hs
  apply Context.deduction
  have he : Context ((graphFormula g u v).encode :: Γ)
      (existsCode 19 (graphBody g u v).encode) := by
    simpa only [graph_code] using (Context.head Γ (graphFormula g u v).encode)
  exact Context.existsElim targetVacuity (Context.under hall _) he

end PASoundness.PAtoCompactGraphContextElim

#print axioms PASoundness.PAtoCompactGraphContextElim.graph_context_elim
#print axioms PASoundness.PAtoCompactGraphContextElim.graph_context_imp
