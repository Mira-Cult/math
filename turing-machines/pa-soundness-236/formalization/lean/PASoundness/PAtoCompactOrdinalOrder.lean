import PASoundness.PAtoCompactQuotientOrder
import PASoundness.PAtoCompactOrdinalEquivalence

/-! Standard-HF calibration of the proposed quotient order on finite ordinal
codes. This is not a K proof of congruence, quotient axioms, induction, or a
PA-to-K proof translation. -/
namespace PASoundness.PAtoCompactOrdinalOrder
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactQuotientOrder PASoundness.PAtoCompactOrdinalEquivalence
open PASoundness.CompactMatrix (Environment bit update decode)
open PASoundness.HFCoding

/-- Standard semantics of the named order proposal, retaining an explicit
representative inside the right-hand operand. -/
theorem less_named_meaning (ρ : Environment) :
    lessFormula.Realize ρ ↔
      ∃ v, bit (ρ 1) v = true ∧ equivalentFormula.Realize (update ρ 1 v) := by
  change (∃ v, ¬ (bit (ρ 1) v = true →
    ¬ (replace 1 7 equivalentFormula).Realize (update ρ 7 v))) ↔ _
  simp only [Classical.not_imp, not_not]
  apply exists_congr
  intro v
  apply and_congr Iff.rfl
  rw [replace_realize 1 7 equivalentFormula representative_fresh.1
    (fun h => representative_fresh.2 (Formula.binders_subset_names _ h))]
  simp only [PASoundness.CompactSemantics.update_same]
  rw [PASoundness.CompactSemantics.update_commute ρ 7 1 v v (by decide)]
  exact Formula.realize_update_fresh equivalentFormula (update ρ 1 v) 7 v representative_fresh.2

/-- The literal compact encoding of the proposed quotient order has the
standard arithmetic less-than meaning on finite ordinal codes. -/
theorem standard_ordinal_order_iff (ρ : Environment) (n m : Nat)
    (h0 : ρ 0 = (ordinal n).code) (h1 : ρ 1 = (ordinal m).code) :
    (decode lessFormula.encode).Realize ρ ↔ n < m := by
  rw [Formula.encode_realize, less_named_meaning]
  constructor
  · rintro ⟨v,hv,hE⟩
    have hm : (⟨v⟩ : Object) ∈ ordinal m := by
      change bit (ordinal m).code v = true
      simpa [h1] using hv
    obtain ⟨k,hk,hv⟩ := (mem_ordinal _ _).mp hm
    have hv' : v = (ordinal k).code := congrArg Object.code hv
    have he := standard_ordinal_iff (update ρ 1 v) n k
      (by simpa [update] using h0) (by simpa [update] using hv')
    rw [Formula.encode_realize] at he
    have hnk := he.mp hE
    simpa [hnk] using hk
  · intro hnm
    let v := (ordinal n).code
    refine ⟨v, ?_, ?_⟩
    · change bit (ρ 1) (ordinal n).code = true
      rw [h1]
      exact ordinal_member hnm
    · have he := standard_ordinal_iff (update ρ 1 v) n n
        (by simpa [update] using h0) (by simp [update, v])
      rw [Formula.encode_realize] at he
      exact he.mpr rfl

end PASoundness.PAtoCompactOrdinalOrder

#print axioms PASoundness.PAtoCompactOrdinalOrder.less_named_meaning
#print axioms PASoundness.PAtoCompactOrdinalOrder.standard_ordinal_order_iff
