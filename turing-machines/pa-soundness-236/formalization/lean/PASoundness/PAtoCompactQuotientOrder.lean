import PASoundness.PAtoCompactOrderIsomorphism

/-! A first-order candidate for the quotient order. It uses an equivalent
representative occurring inside the right-hand set, rather than raw
membership of the left-hand representative. No order, congruence,
arithmetic, induction or full truth theorem is asserted. -/
namespace PASoundness.PAtoCompactQuotientOrder
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.CompactMatrix (Environment bit bit_eq_testBit update)

private def conj (a b : Formula) : Formula := (a.imp b.not).not

set_option maxRecDepth 65536 in
/-- The chosen representative name is absent from the equality formula,
and the replaced input name is not bound there. -/
theorem representative_fresh :
    1 ∉ equivalentFormula.binders ∧ 7 ∉ equivalentFormula.names := by decide

/-- Names 0,1 denote the operands; fresh 7 is the member representative.
`replace` operates on the named syntax, whose bottom node encodes literal
`member 0 0` in K. -/
def lessFormula : Formula := .ex 7
  (conj (.member 1 7) (replace 1 7 equivalentFormula))

theorem less_free : lessFormula.free = {0,1} := by decide

/-- No represented object lies below empty in standard HF semantics. -/
theorem standard_not_less_empty (ρ : Environment) (h : ρ 1 = 0) :
    ¬ lessFormula.Realize ρ := by
  have hf : ∀ v, bit 0 v = false := by intro v; simp [bit_eq_testBit]
  simp [lessFormula, conj, Formula.not, Formula.Realize, update, h, hf]

end PASoundness.PAtoCompactQuotientOrder

#print axioms PASoundness.PAtoCompactQuotientOrder.less_free
#print axioms PASoundness.PAtoCompactQuotientOrder.representative_fresh
#print axioms PASoundness.PAtoCompactQuotientOrder.standard_not_less_empty
