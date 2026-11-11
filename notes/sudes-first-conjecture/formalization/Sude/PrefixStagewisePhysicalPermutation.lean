import Sude.PrefixStagewiseSubsetPermutation

/-! Physical realization of a stage-preserving subset permutation, fixing
all cells outside the selected pair image. -/
namespace Sude
noncomputable section

/-- Install a stage-preserving permutation of supplied pair indices on the
same exact-pool square. Both endpoints move together. Every other cell is
fixed, each stage's endpoint set is preserved, and any common stage gap is
preserved. -/
theorem prefix_reallocate_stagewise_subset {n P Q : ℕ}
    (a : Cell n ≃ Fin (n*n)) (cells : (Fin P × Fin Q) × Bool → Cell n)
    (hcells : Function.Injective cells) (U : Finset (Fin P × Fin Q))
    (e : {z // z ∈ U} ≃ {z // z ∈ U})
    (hstage : ∀ z, (e z).val.1 = z.val.1) :
    ∃ a' : Cell n ≃ Fin (n*n),
      (∀ z (hz : z ∈ U) side,
        entry a' (cells (z,side)) = entry a (cells ((e ⟨z,hz⟩).val,side))) ∧
      (∀ c, c ∉ Set.range (fun x : {z // z ∈ U} × Bool => cells (x.1.val,x.2)) →
        entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin Q × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin Q × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ gap : Fin P → ℕ, (∀ j i, entry a (cells ((j,i),true)) =
          entry a (cells ((j,i),false)) + gap j) →
        ∀ j i, entry a' (cells ((j,i),true)) = entry a' (cells ((j,i),false)) + gap j) := by
  classical
  obtain ⟨ω, hωin, hωout⟩ := prefix_stagewise_subset_permutation U e hstage
  obtain ⟨a', hentry, hfix, hset, hgap⟩ := reallocate_existing_stage_pairs a cells hcells ω
  refine ⟨a', ?_, ?_, hset, hgap⟩
  · rintro ⟨j,i⟩ hi side
    rw [hentry]
    rw [hωin j i hi]
  · intro c hc
    by_cases hr : c ∈ Set.range cells
    · obtain ⟨⟨⟨j,i⟩,side⟩, rfl⟩ := hr
      have hn : (j,i) ∉ U := by
        intro hi
        exact hc ⟨(⟨(j,i),hi⟩,side), rfl⟩
      rw [hentry, hωout j i hn]
    · exact hfix c hr

end
end Sude
