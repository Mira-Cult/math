import PASoundness.PAtoCompactVariableGraphSymmetryClosed
import PASoundness.PAtoCompactVariableGraphSubstitutionConditional
import PASoundness.PAtoCompactDynamicTransitivityFinal

/-! Candidate-relative functionality, source congruence, and output transport
for the variable term graph. Quotient symmetry and transitivity are proved K
derivations, not inputs. Composite term graphs remain separate. -/
namespace PASoundness.PAtoCompactVariableGraphLaws

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactVariableGraphSymmetryClosed
open PASoundness.PAtoCompactVariableGraphSubstitutionConditional
open PASoundness.PAtoCompactDynamicSymmetry PASoundness.PAtoCompactDynamicTransitivityFinal

/-- Under the candidate guard, any two variable-graph outputs are equivalent.
All names may alias; bounds place them below the private allocator block. -/
def variable_functional {α : Type} (v : α → Nat) (a : α) (base x y : Nat)
    (ha : v a < base+2) (hx : x < base+2) (hy : y < base+2) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (termGraph v (.var a) x base).encode
        (imp (termGraph v (.var a) y base).encode (equivAt base x y).encode))) :=
  variable_functional_of_transitivity v a base x y ha hx
    (dynamic_transitivity base x (v a) y hx ha hy)

/-- Quotient-equivalent inputs have quotient-equivalent variable-graph
outputs, under the source candidate guard. -/
def variable_congruence {α : Type} (v : α → Nat) (a b : α) (base x y : Nat)
    (ha : v a < base+2) (hb : v b < base+2)
    (hx : x < base+2) (hy : y < base+2) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) (v b)).encode
        (imp (termGraph v (.var a) x base).encode
          (imp (termGraph v (.var b) y base).encode (equivAt base x y).encode)))) :=
  variable_congruence_of_transitivity v a b base x y ha hx
    (dynamic_transitivity base x (v a) (v b) hx ha hb)
    (dynamic_transitivity base x (v b) y hx hb hy)

/-- Transport a variable graph along a variable graph at its output. -/
def variable_output_forward {α : Type} (v : α → Nat) (a : α) (base q r : Nat)
    (ha : v a < base+2) (hq : q < base+2) (hr : r < base+2) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (termGraph v (.var a) q base).encode
        (imp (termGraph id (.var q : Peano.Term) r base).encode
          (termGraph v (.var a) r base).encode))) :=
  variable_graph_output_transport v a base q r
    (dynamic_transitivity base (v a) q r ha hq hr)

/-- Reverse output transport also retains the required candidate guard at q. -/
def variable_output_reverse {α : Type} (v : α → Nat) (a : α) (base q r : Nat)
    (ha : v a < base+2) (hq : q < base+2) (hr : r < base+2) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (domainAt base q).encode
        (imp (termGraph id (.var q : Peano.Term) r base).encode
          (imp (termGraph v (.var a) r base).encode
            (termGraph v (.var a) q base).encode)))) :=
  variable_graph_output_transport_reverse v a base q r
    (dynamic_symmetry base q r hq hr)
    (dynamic_transitivity base (v a) r q ha hr hq)

end PASoundness.PAtoCompactVariableGraphLaws

#print axioms PASoundness.PAtoCompactVariableGraphLaws.variable_functional
#print axioms PASoundness.PAtoCompactVariableGraphLaws.variable_congruence
#print axioms PASoundness.PAtoCompactVariableGraphLaws.variable_output_forward
#print axioms PASoundness.PAtoCompactVariableGraphLaws.variable_output_reverse
