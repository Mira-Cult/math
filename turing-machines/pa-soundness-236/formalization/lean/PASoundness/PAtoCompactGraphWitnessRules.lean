import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Literal finite-K introduction/elimination rules for the exact candidate
Kuratowski graph's pair witness. No graph existence, pair-coordinate
uniqueness, or full interpretation is asserted. Code 1 remains literal K
falsum; no semantic soundness theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGraphWitnessRules
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The literal graph body with its pair-witness name 19 exposed. -/
def graphBody (g u v : Nat) : Formula :=
  Formula.imp (Formula.imp (.member g 19) (.imp (pairFormula 19 u v) .bottom)) .bottom

/-- Exposing the graph witness yields precisely this compact conjunction. -/
theorem graph_body_code (g u v : Nat) :
    (graphBody g u v).encode = both (member g 19) (pairFormula 19 u v).encode := rfl

/-- The exact graph is the existential closure of the displayed body. -/
theorem graph_code (g u v : Nat) :
    (graphFormula g u v).encode = existsCode 19 (graphBody g u v).encode := rfl

/-- Derive a graph once an explicit pair witness is known to be a member.
Names 19–22 are graph/pair binders; if this formula is read as an ordinary
relation on g,u,v, those parameters must avoid the internal binder names. -/
def graph_intro (g u v : Nat) : KDerivation
    (imp (both (member g 19) (pairFormula 19 u v).encode) (graphFormula g u v).encode) := by
  have hb : 19 ∉ (graphBody g u v).binders := by
    change 19 ∉ ({20, 21, 22} : Finset Nat)
    decide
  have hi := existsIntroduce 19 (graphBody g u v) hb
  simpa only [graph_body_code, graph_code] using hi

/-- Eliminate the exact graph's pair witness when the target formula has no
occurrence of witness label 19 and a supplied finite K proof derives that
target from the exposed body. The explicit proof argument is an object-level
K derivation, not a semantic premise. -/
def graph_elim_with_vacuity (g u v : Nat) (target : Formula)
    (vacuity : KDerivation (imp target.encode (allCode 19 target.encode)))
    (step : KDerivation (imp (both (member g 19) (pairFormula 19 u v).encode) target.encode)) :
    KDerivation (imp (graphFormula g u v).encode target.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have he : Context [(graphFormula g u v).encode] (existsCode 19 (graphBody g u v).encode) := by
    simpa only [graph_code] using (Context.head [] (graphFormula g u v).encode)
  have hs : KDerivation (imp (graphBody g u v).encode target.encode) := by
    simpa only [graph_body_code] using step
  exact Context.existsElim vacuity (.closed (.generalize 19 hs)) he

def graph_elim (g u v : Nat) (target : Formula) (fresh : 19 ∉ target.names)
    (step : KDerivation (imp (both (member g 19) (pairFormula 19 u v).encode) target.encode)) :
    KDerivation (imp (graphFormula g u v).encode target.encode) :=
  graph_elim_with_vacuity g u v target (target.vacuity 19 fresh) step

theorem graph_elim_with_vacuity_certificate (g u v : Nat) (target : Formula)
    (vacuity : KDerivation (imp target.encode (allCode 19 target.encode)))
    (step : KDerivation (imp (both (member g 19) (pairFormula 19 u v).encode) target.encode)) :
    theoremCode (certificate (graph_elim_with_vacuity g u v target vacuity step)) =
      imp (graphFormula g u v).encode target.encode :=
  certificate_correct (graph_elim_with_vacuity g u v target vacuity step)

theorem graph_elim_certificate (g u v : Nat) (target : Formula) (fresh : 19 ∉ target.names)
    (step : KDerivation (imp (both (member g 19) (pairFormula 19 u v).encode) target.encode)) :
    theoremCode (certificate (graph_elim g u v target fresh step)) =
      imp (graphFormula g u v).encode target.encode :=
  certificate_correct (graph_elim g u v target fresh step)

end PASoundness.PAtoCompactGraphWitnessRules

#print axioms PASoundness.PAtoCompactGraphWitnessRules.graph_intro
#print axioms PASoundness.PAtoCompactGraphWitnessRules.graph_elim_with_vacuity
#print axioms PASoundness.PAtoCompactGraphWitnessRules.graph_elim_with_vacuity_certificate
#print axioms PASoundness.PAtoCompactGraphWitnessRules.graph_elim
#print axioms PASoundness.PAtoCompactGraphWitnessRules.graph_elim_certificate
