import PASoundness.PAtoCompactOrderIsomorphism

/-! Conditional standard-HF semantic reading of the candidate order clause.
The two hypotheses identify its graph instances with the same relation; they
must be supplied separately. No K quotient or order theorem is asserted. -/
namespace PASoundness.PAtoCompactOrderMeaning
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.CompactMatrix (Environment bit update)

private def andF (a b : Formula) : Formula := (a.imp b.not).not
private def iffF (a b : Formula) : Formula := andF (a.imp b) (b.imp a)

theorem order_meaning (η : Environment) (R : Nat → Nat → Nat → Prop)
    (h23 : ∀ ρ, (graphFormula 6 2 3).Realize ρ ↔ R (ρ 6) (ρ 2) (ρ 3))
    (h45 : ∀ ρ, (graphFormula 6 4 5).Realize ρ ↔ R (ρ 6) (ρ 4) (ρ 5)) :
    orderFormula.Realize η ↔
      ∀ a c b d, bit (η 0) a = true → bit (η 0) c = true →
        bit (η 1) b = true → bit (η 1) d = true →
        R (η 6) a b → R (η 6) c d →
        (bit c a = true ↔ bit d b = true) := by
  change (Formula.all 2 (Formula.all 4 (Formula.all 3 (Formula.all 5
    (.imp (andF (.member 0 2) (andF (.member 0 4)
      (andF (.member 1 3) (andF (.member 1 5)
        (andF (graphFormula 6 2 3) (graphFormula 6 4 5))))))
      (iffF (.member 4 2) (.member 5 3))))))).Realize η ↔ _
  simp [andF, iffF, Formula.Realize, Formula.not, h23, h45, update]
  constructor
  · intro H a c b d ha hc hb hd hab hcd
    have he := H a c b d ha hc hb hd hab hcd
    exact Bool.eq_iff_iff.mpr ⟨he.1, he.2⟩
  · intro H a c b d ha hc hb hd hab hcd
    have he := Bool.eq_iff_iff.mp (H a c b d ha hc hb hd hab hcd)
    exact ⟨he.mp, he.mpr⟩

end PASoundness.PAtoCompactOrderMeaning

#print axioms PASoundness.PAtoCompactOrderMeaning.order_meaning
