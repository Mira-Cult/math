import Sude.StagePairReallocation

/-! Extending a stage-preserving permutation of selected slots to full
stagewise permutations, fixing every slot outside the selected set. -/
namespace Sude
noncomputable section

/-- A permutation on a finite subset of stage/index slots, preserving the
stage coordinate, extends to one permutation per stage and fixes all slots
outside the subset. This is a combinatorial interface; it does not itself
realize a physical placement. -/
theorem prefix_stagewise_subset_permutation {P Q : ℕ}
    (U : Finset (Fin P × Fin Q)) (e : {z // z ∈ U} ≃ {z // z ∈ U})
    (hstage : ∀ z, (e z).val.1 = z.val.1) :
    ∃ ω : Fin P → Equiv.Perm (Fin Q),
      (∀ j i (hi : (j,i) ∈ U), (j, ω j i) = (e ⟨(j,i),hi⟩).val) ∧
      (∀ j i, (j,i) ∉ U → ω j i = i) := by
  classical
  let emb : {z // z ∈ U} ↪ (Fin P × Fin Q) := ⟨Subtype.val, Subtype.val_injective⟩
  let σ : Equiv.Perm (Fin P × Fin Q) := Equiv.Perm.viaFintypeEmbedding e emb
  have hin (z : {z // z ∈ U}) : σ z.val = (e z).val := by
    simpa [σ, emb] using Equiv.Perm.viaFintypeEmbedding_apply_image e emb z
  have hout (z : Fin P × Fin Q) (hz : z ∉ U) : σ z = z := by
    have hn : z ∉ Set.range emb := by
      rintro ⟨t, ht⟩
      exact hz (ht ▸ t.property)
    exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range e emb hn
  have hfst (z : Fin P × Fin Q) : (σ z).1 = z.1 := by
    by_cases hz : z ∈ U
    · simpa [hin ⟨z,hz⟩] using hstage ⟨z,hz⟩
    · rw [hout z hz]
  have hinvfst (z : Fin P × Fin Q) : (σ.symm z).1 = z.1 := by
    have h := hfst (σ.symm z)
    simpa using h.symm
  have hpair (j : Fin P) (i : Fin Q) : σ (j,i) = (j, (σ (j,i)).2) := by
    exact Prod.ext (hfst (j,i)) rfl
  have hinvpair (j : Fin P) (i : Fin Q) : σ.symm (j,i) = (j, (σ.symm (j,i)).2) := by
    exact Prod.ext (hinvfst (j,i)) rfl
  let ω : Fin P → Equiv.Perm (Fin Q) := fun j =>
    { toFun := fun i => (σ (j,i)).2
      invFun := fun i => (σ.symm (j,i)).2
      left_inv := by
        intro i
        have h := congrArg Prod.snd (σ.symm_apply_apply (j,i))
        rw [hpair j i] at h
        exact h
      right_inv := by
        intro i
        have h := congrArg Prod.snd (σ.apply_symm_apply (j,i))
        rw [hinvpair j i] at h
        exact h }
  refine ⟨ω, ?_, ?_⟩
  · intro j i hi
    exact (hpair j i).symm.trans (hin ⟨(j,i),hi⟩)
  · intro j i hi
    have h := congrArg Prod.snd (hout (j,i) hi)
    exact h

end
end Sude
