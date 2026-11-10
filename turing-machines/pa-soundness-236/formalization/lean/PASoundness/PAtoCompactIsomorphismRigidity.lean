import PASoundness.PAtoCompactOrdinalBijection
import PASoundness.PAtoCompactBijectionMeaning

/-! A conditional standard-HF rigidity result for the specific proposed
isomorphism formula. The displayed graph-semantics hypotheses must still be
proved for the concrete pair-based graph formula. It is not a K derivation,
a quotient congruence theorem, or an arithmetic interpretation. -/
namespace PASoundness.PAtoCompactIsomorphismRigidity
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactBijectionMeaning PASoundness.PAtoCompactOrdinalBijection
open PASoundness.CompactMatrix (Environment update)
open PASoundness.HFCoding

theorem ordinal_rigidity (ρ : Environment) (n m : Nat) (R : Nat → Nat → Nat → Prop)
    (h0 : ρ 0 = (ordinal n).code) (h1 : ρ 1 = (ordinal m).code)
    (h23 : ∀ η, (graphFormula 6 2 3).Realize η ↔ R (η 6) (η 2) (η 3))
    (h24 : ∀ η, (graphFormula 6 2 4).Realize η ↔ R (η 6) (η 2) (η 4))
    (h43 : ∀ η, (graphFormula 6 4 3).Realize η ↔ R (η 6) (η 4) (η 3))
    (hE : equivalentFormula.Realize ρ) : n = m := by
  change ∃ g, ((bijectionFormula.imp orderFormula.not).not).Realize (update ρ 6 g) at hE
  obtain ⟨g,h⟩ := hE
  change ¬ (bijectionFormula.Realize (update ρ 6 g) →
    ¬ orderFormula.Realize (update ρ 6 g)) at h
  have hbi : bijectionFormula.Realize (update ρ 6 g) := by
    by_contra hn
    exact h (fun hb => False.elim (hn hb))
  have hb := (bijection_meaning (update ρ 6 g) R h23 h24 h43).mp hbi
  apply ordinal_bijection_cardinality n m (R g)
  · simpa [update, h0, h1] using hb.1
  · simpa [update, h0, h1] using hb.2

end PASoundness.PAtoCompactIsomorphismRigidity

#print axioms PASoundness.PAtoCompactIsomorphismRigidity.ordinal_rigidity
