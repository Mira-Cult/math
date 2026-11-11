import Sude.DoublePairBatch

/-! Iterate a proved fresh-block supply with a single global deletion budget. -/
namespace Sude
noncomputable section

/-- A double block consumes at most four distinct entries. -/
theorem DoublePair.footprint_card_le_four (b : DoublePair) : b.footprint.card ≤ 4 := by
  have h₁ := Finset.card_insert_le b.low₁ ({b.low₂, b.high₁, b.high₂} : Finset ℕ)
  have h₂ := Finset.card_insert_le b.low₂ ({b.high₁, b.high₂} : Finset ℕ)
  have h₃ := Finset.card_insert_le b.high₁ ({b.high₂} : Finset ℕ)
  simp only [Finset.card_singleton] at h₃
  change ({b.low₁, b.low₂, b.high₁, b.high₂} : Finset ℕ).card ≤ 4
  omega

/-- Any proved fresh-block supply that survives an arbitrary global deletion
set up to `B` yields `k` mutually disjoint blocks, avoiding the original
reservations, provided four entries per selected block are budgeted. -/
theorem select_double_pairs_from_depletion_supply
    (P : DoublePair → Prop) (B k : ℕ) (removed : Finset ℕ)
    (hsupply : ∀ R : Finset ℕ, R.card ≤ B →
      ∃ b : DoublePair, P b ∧ Disjoint b.footprint R)
    (hbudget : removed.card + 4 * k ≤ B) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, P b) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint removed) := by
  induction k generalizing removed with
  | zero => exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨b, hbP, hbavoid⟩ := hsupply removed (by omega)
    let next := removed ∪ b.footprint
    have hnextcard : next.card ≤ removed.card + 4 := by
      calc
        _ ≤ removed.card + b.footprint.card := Finset.card_union_le _ _
        _ ≤ removed.card + 4 := Nat.add_le_add_left b.footprint_card_le_four _
    have hnextbudget : next.card + 4 * k ≤ B := by omega
    obtain ⟨blocks, hlen, hvalid, hpair, havoid⟩ := ih next hnextbudget
    refine ⟨b :: blocks, by simp [hlen], ?_, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hbP
      · exact hvalid c hc
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hpair⟩
      intro c hc
      exact (Disjoint.mono_right (Finset.subset_union_right : b.footprint ⊆ next)
        (havoid c hc)).symm
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hbavoid
      · exact Disjoint.mono_right (Finset.subset_union_left : removed ⊆ next) (havoid c hc)

end
end Sude
