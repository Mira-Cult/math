import PASoundness.PAtoCompactGraphMeaning
import PASoundness.PAtoCompactDiagonalGraph
import PASoundness.PAtoCompactBijectionMeaning
import PASoundness.PAtoCompactOrderMeaning

/-! Standard-HF reflexivity of the concrete candidate equality formula using
an explicitly represented diagonal graph. This semantic fact is not a K
proof of reflexivity or an arithmetic interpretation. -/
namespace PASoundness.PAtoCompactStandardReflexivity
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphMeaning PASoundness.PAtoCompactDiagonalGraph
open PASoundness.PAtoCompactBijectionMeaning PASoundness.PAtoCompactOrderMeaning
open PASoundness.CompactMatrix (Environment bit update)
open PASoundness.HFCoding

/-- The represented diagonal graph denotes the identity on the members of x. -/
theorem diagonal_graphRel (x a b : Nat) :
    graphRel (diagonalGraph ⟨x⟩).code a b ↔ bit x a = true ∧ a = b := by
  change PASoundness.PAtoCompactOrderedPair.orderedPair ⟨a⟩ ⟨b⟩ ∈ diagonalGraph ⟨x⟩ ↔ _
  have h := diagonal_membership ⟨x⟩ ⟨a⟩ ⟨b⟩
  change PASoundness.PAtoCompactOrderedPair.orderedPair ⟨a⟩ ⟨b⟩ ∈ diagonalGraph ⟨x⟩ ↔
    bit x a = true ∧ (⟨a⟩ : Object) = ⟨b⟩ at h
  simpa only [Object.mk.injEq] using h

/-- For every standard HF object, the concrete named equivalence formula is
true when its two inputs denote that object. The witness is an explicitly
assembled finite diagonal graph. -/
theorem standard_reflexive (ρ : Environment) (h : ρ 0 = ρ 1) :
    equivalentFormula.Realize ρ := by
  classical
  let G := (diagonalGraph ⟨ρ 0⟩).code
  let η := update ρ 6 G
  have hg23 : ∀ σ, (graphFormula 6 2 3).Realize σ ↔ graphRel (σ 6) (σ 2) (σ 3) := by
    intro σ; exact graphFormula_realize_iff 6 2 3 σ (by decide) (by decide) (by decide)
  have hg24 : ∀ σ, (graphFormula 6 2 4).Realize σ ↔ graphRel (σ 6) (σ 2) (σ 4) := by
    intro σ; exact graphFormula_realize_iff 6 2 4 σ (by decide) (by decide) (by decide)
  have hg43 : ∀ σ, (graphFormula 6 4 3).Realize σ ↔ graphRel (σ 6) (σ 4) (σ 3) := by
    intro σ; exact graphFormula_realize_iff 6 4 3 σ (by decide) (by decide) (by decide)
  have hg45 : ∀ σ, (graphFormula 6 4 5).Realize σ ↔ graphRel (σ 6) (σ 4) (σ 5) := by
    intro σ; exact graphFormula_realize_iff 6 4 5 σ (by decide) (by decide) (by decide)
  have hv0 : η 0 = ρ 0 := by simp [η]
  have hv1 : η 1 = ρ 0 := by simp [η, ← h]
  have hv6 : η 6 = G := by simp [η]
  have hd (a b : Nat) : graphRel (η 6) a b ↔ bit (ρ 0) a = true ∧ a = b := by
    rw [hv6]; exact diagonal_graphRel (ρ 0) a b
  have hb : bijectionFormula.Realize η := by
    apply (bijection_meaning η graphRel hg23 hg24 hg43).mpr
    constructor
    · intro a ha
      have ha' : bit (ρ 0) a = true := by simpa [hv0] using ha
      refine ⟨a, ?_, (hd a a).mpr ⟨ha', rfl⟩, ?_⟩
      · simpa [hv1] using ha'
      · intro b' _ hb'
        exact ((hd a b').mp hb').2.symm
    · intro b hb'
      have hb'' : bit (ρ 0) b = true := by simpa [hv1] using hb'
      refine ⟨b, ?_, (hd b b).mpr ⟨hb'', rfl⟩, ?_⟩
      · simpa [hv0] using hb''
      · intro a' _ ha'
        exact ((hd a' b).mp ha').2
  have ho : orderFormula.Realize η := by
    apply (order_meaning η graphRel hg23 hg45).mpr
    intro a c b d _ _ _ _ hab hcd
    have he1 := ((hd a b).mp hab).2
    have he2 := ((hd c d).mp hcd).2
    subst b
    subst d
    rfl
  change ∃ g, ¬ (bijectionFormula.Realize (update ρ 6 g) →
    ¬ orderFormula.Realize (update ρ 6 g))
  exact ⟨G, fun h' => h' hb ho⟩

/-- The same standard-HF property for the literal compact encoding. -/
theorem standard_reflexive_encoded (ρ : Environment) (h : ρ 0 = ρ 1) :
    (PASoundness.CompactMatrix.decode equivalentFormula.encode).Realize ρ :=
  (Formula.encode_realize equivalentFormula ρ).mpr (standard_reflexive ρ h)

end PASoundness.PAtoCompactStandardReflexivity

#print axioms PASoundness.PAtoCompactStandardReflexivity.standard_reflexive_encoded
