import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactOrderIsoInverseGlobal
import PASoundness.CompactFreshen

/-! Syntactic vacuity for names that are bound, rather than absent, in the
exact order and inverse formulas. Freshening yields bidirectional K proof
data; no semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInverseGlobal
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Transport literal vacuity across a supplied K proof equivalence. -/
def vacuity_of_equiv (f f' : Formula) (h : ProofEquiv f f') (v : Nat)
    (fresh : v ∉ f'.names) : KDerivation (imp f.encode (allCode v f.encode)) :=
  compose h.forward (compose (f'.vacuity v fresh) (allCongr v h.backward))

private theorem order_names_lt : ∀ v ∈ orderFormula.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ orderFormula.names.sup id at hm
  have hb : orderFormula.names.sup id < 30 := by decide
  omega

private theorem reverse_names_lt : ∀ v ∈ reverseFamily.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ reverseFamily.names.sup id at hm
  have hb : reverseFamily.names.sup id < 30 := by decide
  omega

def freshOrder := freshen orderFormula 30 order_names_lt
def freshReverse := freshen reverseFamily 30 reverse_names_lt

/-- The quantified order formula is vacuous in these four names after
capture-safe freshening; the supplied evidence is a decidable syntactic fact. -/
def order_vacuity (v : Nat) (fresh : v ∉ freshOrder.formula.names) :
    KDerivation (imp orderFormula.encode (allCode v orderFormula.encode)) :=
  vacuity_of_equiv orderFormula freshOrder.formula freshOrder.equivalent v fresh

/-- The global inverse family likewise has no free coordinate names. -/
def reverse_vacuity (v : Nat) (fresh : v ∉ freshReverse.formula.names) :
    KDerivation (imp reverseFamily.encode (allCode v reverseFamily.encode)) :=
  vacuity_of_equiv reverseFamily freshReverse.formula freshReverse.equivalent v fresh

theorem order_fresh_2 : 2 ∉ freshOrder.formula.names := by decide
theorem order_fresh_3 : 3 ∉ freshOrder.formula.names := by decide
theorem order_fresh_4 : 4 ∉ freshOrder.formula.names := by decide
theorem order_fresh_5 : 5 ∉ freshOrder.formula.names := by decide
theorem reverse_fresh_2 : 2 ∉ freshReverse.formula.names := by decide
theorem reverse_fresh_3 : 3 ∉ freshReverse.formula.names := by decide
theorem reverse_fresh_4 : 4 ∉ freshReverse.formula.names := by decide
theorem reverse_fresh_5 : 5 ∉ freshReverse.formula.names := by decide

end PASoundness.PAtoCompactOrderIsoVacuity

#print axioms PASoundness.PAtoCompactOrderIsoVacuity.order_vacuity
#print axioms PASoundness.PAtoCompactOrderIsoVacuity.reverse_vacuity
