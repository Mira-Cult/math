import PASoundness.PAtoCompactCandidateDynamicReflexivity

/-! The variable-graph existence result for an arbitrary source-variable
carrier and name map. The map need not be injective. -/
namespace PASoundness.PAtoCompactVariableTotalityGeneral

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactCandidateDynamicReflexivity

/-- A variable graph has a value using the variable's own value as witness.
The source and witness names are distinct, but assigned values may coincide. -/
def variable_graph_total {α : Type} (v : α → Nat) (p : α) (b o : Nat)
    (hp : v p < b) (ho : o < b) (hop : o ≠ v p) :
    KDerivation (imp (domainAt b (v p)).encode
      (existsCode o (termGraph v (.var p : Peano.language.Term α) o b).encode)) := by
  simpa only [termGraph] using
    PAtoCompactCandidateDynamicReflexivity.variable_graph_total b (v p) o hp ho hop

theorem variable_graph_total_certificate {α : Type} (v : α → Nat) (p : α) (b o : Nat)
    (hp : v p < b) (ho : o < b) (hop : o ≠ v p) :
    theoremCode (certificate (variable_graph_total v p b o hp ho hop)) =
      imp (domainAt b (v p)).encode
        (existsCode o (termGraph v (.var p : Peano.language.Term α) o b).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactVariableTotalityGeneral

#print axioms PASoundness.PAtoCompactVariableTotalityGeneral.variable_graph_total
#print axioms PASoundness.PAtoCompactVariableTotalityGeneral.variable_graph_total_certificate
