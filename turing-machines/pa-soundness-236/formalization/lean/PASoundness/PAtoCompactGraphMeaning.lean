import PASoundness.PAtoCompactPairMeaning

/-! Standard-HF meaning of the proposed represented graph formula. This
uses extensional HF semantics and is not a K derivation. -/
namespace PASoundness.PAtoCompactGraphMeaning
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPairMeaning PASoundness.PAtoCompactOrderedPair
open PASoundness.CompactMatrix (Environment bit update)

/-- Semantic graph membership in the canonical Kuratowski pair, on raw HF
codes. This relation is separate from K syntactic derivability. -/
def graphRel (g a b : Nat) : Prop := bit g (orderedPair ⟨a⟩ ⟨b⟩).code = true

private def andF (a b : Formula) : Formula := (a.imp b.not).not

/-- The literal graph formula has the claimed graph relation meaning when
its visible names avoid the internal witness and pair binders. -/
theorem graphFormula_realize_iff (g a b : Nat) (ρ : Environment)
    (hg : g ≠ 19)
    (ha : a ≠ 19 ∧ a ≠ 20 ∧ a ≠ 21 ∧ a ≠ 22)
    (hb : b ≠ 19 ∧ b ≠ 20 ∧ b ≠ 21 ∧ b ≠ 22) :
    (graphFormula g a b).Realize ρ ↔ graphRel (ρ g) (ρ a) (ρ b) := by
  have hp : (19 : Nat) ≠ 20 ∧ 19 ≠ 21 ∧ 19 ≠ 22 := by decide
  change (Formula.ex 19 (andF (.member g 19) (pairFormula 19 a b))).Realize ρ ↔ _
  simp [andF, Formula.Realize, Formula.not,
    pairFormula_realize_iff 19 a b _ hp ⟨ha.2.1, ha.2.2.1, ha.2.2.2⟩
      ⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩, update, hg, ha.1, hb.1, graphRel]

end PASoundness.PAtoCompactGraphMeaning

#print axioms PASoundness.PAtoCompactGraphMeaning.graphFormula_realize_iff
