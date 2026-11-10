import PASoundness.PAtoCompactVariableGraphFunctionalConditional
import PASoundness.PAtoCompactDynamicSymmetry

/-! Variable graph functionality and congruence after supplying the proved
candidate-relative quotient symmetry. Transitivity remains an explicit finite
K proof input; this module does not establish it or composite-term functionality. -/
namespace PASoundness.PAtoCompactVariableGraphSymmetryClosed

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactVariableGraphFunctionalConditional
open PASoundness.PAtoCompactDynamicSymmetry

/-- The two values of a variable graph are equivalent under a candidate
source guard, conditional only on the displayed quotient transitivity proof. -/
def variable_functional_of_transitivity {α : Type} (v : α → Nat) (a : α)
    (base x y : Nat) (ha : v a < base+2) (hx : x < base+2)
    (trans : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v a)).encode
        (imp (equivAt base (v a) y).encode (equivAt base x y).encode)))) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (termGraph v (.var a) x base).encode
        (imp (termGraph v (.var a) y base).encode (equivAt base x y).encode))) :=
  variable_graph_functional v a base x y (dynamic_symmetry base (v a) x ha hx) trans

/-- Graphs at quotient-equivalent variable names have quotient-equivalent
outputs, conditional only on the two displayed transitivity proofs. -/
def variable_congruence_of_transitivity {α : Type} (v : α → Nat) (a b : α)
    (base x y : Nat) (ha : v a < base+2) (hx : x < base+2)
    (trans₁ : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v a)).encode
        (imp (equivAt base (v a) (v b)).encode (equivAt base x (v b)).encode))))
    (trans₂ : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v b)).encode
        (imp (equivAt base (v b) y).encode (equivAt base x y).encode)))) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) (v b)).encode
        (imp (termGraph v (.var a) x base).encode
          (imp (termGraph v (.var b) y base).encode (equivAt base x y).encode)))) :=
  variable_graph_congruence v a b base x y (dynamic_symmetry base (v a) x ha hx) trans₁ trans₂

end PASoundness.PAtoCompactVariableGraphSymmetryClosed

#print axioms PASoundness.PAtoCompactVariableGraphSymmetryClosed.variable_functional_of_transitivity
#print axioms PASoundness.PAtoCompactVariableGraphSymmetryClosed.variable_congruence_of_transitivity
