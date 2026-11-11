import Sude.PermutedSeedPlacement
import Sude.Placement

/-! Reallocate already installed pairs, keeping both endpoints together.
No unused-candidate or new-value assumptions are needed. -/
namespace Sude
noncomputable section

/-- Independently permuting the pairs of every stage can be realized on an
existing exact-pool square. The entire complement of the supplied physical
slot image is fixed, and each stage retains exactly its original endpoint
set. If the old stage pairs have a common gap, the new pairs have that gap.
This does not assert any geometric, line-balance, or allocation property. -/
theorem reallocate_existing_stage_pairs {n P Q : ℕ}
    (a : Cell n ≃ Fin (n * n))
    (cells : (Fin P × Fin Q) × Bool → Cell n)
    (hcells : Function.Injective cells)
    (ω : Fin P → Equiv.Perm (Fin Q)) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ j i side, entry a' (cells ((j, i), side)) =
        entry a (cells ((j, ω j i), side))) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin Q × Bool =>
        entry a' (cells ((j, x.1), x.2))) =
        Finset.univ.image (fun x : Fin Q × Bool =>
        entry a (cells ((j, x.1), x.2)))) ∧
      (∀ gap : Fin P → ℕ, (∀ j i,
        entry a (cells ((j, i), true)) = entry a (cells ((j, i), false)) + gap j) →
        ∀ j i, entry a' (cells ((j, i), true)) =
          entry a' (cells ((j, i), false)) + gap j) := by
  classical
  let embedding : ((Fin P × Fin Q) × Bool) ↪ Cell n := ⟨cells, hcells⟩
  let σ : Equiv.Perm (Cell n) := Equiv.Perm.viaFintypeEmbedding (stagePairPermutation ω) embedding
  let a' : Cell n ≃ Fin (n * n) := σ.trans a
  have hentry : ∀ j i side, entry a' (cells ((j, i), side)) =
      entry a (cells ((j, ω j i), side)) := by
    intro j i side
    have hσ : σ (cells ((j, i), side)) = cells ((j, ω j i), side) := by
      simpa [σ, embedding, stagePairPermutation] using
        (Equiv.Perm.viaFintypeEmbedding_apply_image
          (stagePairPermutation ω) embedding ((j, i), side))
    simp [a', entry, hσ]
  refine ⟨a', hentry, ?_, ?_, ?_⟩
  · intro c hc
    have hσ : σ c = c := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
        (stagePairPermutation ω) embedding hc
    simp [a', entry, hσ]
  · intro j
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, side⟩, h⟩
      exact ⟨(ω j i, side), by simpa [hentry] using h⟩
    · rintro ⟨⟨i, side⟩, h⟩
      refine ⟨((ω j).symm i, side), ?_⟩
      simpa [hentry] using h
  · intro gap hgap j i
    simpa only [hentry] using hgap j (ω j i)

end
end Sude
