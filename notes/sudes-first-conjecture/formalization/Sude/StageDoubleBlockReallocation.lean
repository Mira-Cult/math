import Sude.StagePairReallocation

/-! Reallocate existing double blocks without separating their constituent
pairs. No concentration, grid, theta, or line property is asserted. -/
namespace Sude
noncomputable section

/-- A stage-wise block permutation, followed by an independently chosen
pair permutation for each destination block; endpoint orientation is fixed. -/
def stageDoubleBlockPermutation {P B : ℕ}
    (ω : Fin P → Equiv.Perm (Fin B)) (τ : Fin P → Fin B → Equiv.Perm (Fin 2)) :
    Equiv.Perm ((Fin P × Fin B × Fin 2) × Bool) where
  toFun x := ((x.1.1, ω x.1.1 x.1.2.1, τ x.1.1 x.1.2.1 x.1.2.2), x.2)
  invFun x :=
    let b := (ω x.1.1).symm x.1.2.1
    ((x.1.1, b, (τ x.1.1 b).symm x.1.2.2), x.2)
  left_inv := by
    rintro ⟨⟨j, b, p⟩, side⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨j, b, p⟩, side⟩
    simp only [Equiv.apply_symm_apply]

/-- The supplied stage/block and internal-pair permutations are realized on
one existing square. Each stage keeps its endpoint set, the complement of
physical slots is fixed, and each destination inherits the common gap of its
selected source block. No gap is claimed to stay at a destination index. -/
theorem reallocate_existing_stage_double_blocks {n P B : ℕ}
    (a : Cell n ≃ Fin (n * n))
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (hcells : Function.Injective cells)
    (ω : Fin P → Equiv.Perm (Fin B)) (τ : Fin P → Fin B → Equiv.Perm (Fin 2)) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ j b p side, entry a' (cells ((j, b, p), side)) =
        entry a (cells ((j, ω j b, τ j b p), side))) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry a' (cells ((j, x.1.1, x.1.2), x.2))) =
        Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry a (cells ((j, x.1.1, x.1.2), x.2)))) ∧
      (∀ gap : Fin P → Fin B → ℕ, (∀ j b p,
        entry a (cells ((j, b, p), true)) = entry a (cells ((j, b, p), false)) + gap j b) →
        ∀ j b p, entry a' (cells ((j, b, p), true)) =
          entry a' (cells ((j, b, p), false)) + gap j (ω j b)) := by
  classical
  let embedding : ((Fin P × Fin B × Fin 2) × Bool) ↪ Cell n := ⟨cells, hcells⟩
  let σ : Equiv.Perm (Cell n) := Equiv.Perm.viaFintypeEmbedding (stageDoubleBlockPermutation ω τ) embedding
  let a' : Cell n ≃ Fin (n * n) := σ.trans a
  have hentry : ∀ j b p side, entry a' (cells ((j, b, p), side)) =
      entry a (cells ((j, ω j b, τ j b p), side)) := by
    intro j b p side
    have hσ : σ (cells ((j, b, p), side)) = cells ((j, ω j b, τ j b p), side) := by
      simpa [σ, embedding, stageDoubleBlockPermutation] using
        (Equiv.Perm.viaFintypeEmbedding_apply_image
          (stageDoubleBlockPermutation ω τ) embedding ((j, b, p), side))
    simp [a', entry, hσ]
  refine ⟨a', hentry, ?_, ?_, ?_⟩
  · intro c hc
    have hσ : σ c = c := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
        (stageDoubleBlockPermutation ω τ) embedding hc
    simp [a', entry, hσ]
  · intro j
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨b, p⟩, side⟩, h⟩
      exact ⟨((ω j b, τ j b p), side), by simpa [hentry] using h⟩
    · rintro ⟨⟨⟨b, p⟩, side⟩, h⟩
      let b' := (ω j).symm b
      refine ⟨((b', (τ j b').symm p), side), ?_⟩
      simpa [hentry, b'] using h
  · intro gap hgap j b p
    simpa only [hentry] using hgap j (ω j b) (τ j b p)

end
end Sude
