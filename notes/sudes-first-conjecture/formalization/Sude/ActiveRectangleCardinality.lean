import Sude.ActiveRectangleLineCounts

/-! Cardinality of an explicitly selected family of full packed rectangles. -/
namespace Sude
noncomputable section

/-- Four distinct corners occur for each selected packed rectangle. -/
theorem active_rectangle_support_card {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) :
    (activeRectangleSupport hs choice active).card = 4 * active.card := by
  classical
  unfold activeRectangleSupport
  rw [Finset.card_image_of_injective _ (packedRectangleCorner_injective hs choice)]
  simp [Nat.mul_comm]

end
end Sude
