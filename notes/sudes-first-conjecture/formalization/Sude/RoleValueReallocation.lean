import Sude.FWGrownRoleValueUnion
import Sude.FWSeedReallocationGrowthPreservation

/-! Value images under supplied reallocation of a subset of role cells. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Replacing values within a subset while preserving its value image and
fixing the rest preserves the value image of the whole finite support. -/
theorem role_value_image_preserved {α β : Type*} [DecidableEq α] [DecidableEq β]
    (roles seed : Finset α) (before after : α → β) (hsub : seed ⊆ roles)
    (hfixed : ∀ c ∈ roles, c ∉ seed → after c = before c)
    (hseed : seed.image after = seed.image before) :
    roles.image after = roles.image before := by
  classical
  have hsplit : seed ∪ (roles \ seed) = roles := Finset.union_sdiff_of_subset hsub
  rw [← hsplit, Finset.image_union, Finset.image_union, hseed]
  congr 1
  apply Finset.image_congr
  intro c hc
  exact hfixed c (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hc).2

/-- An indexed seed reallocation with the existing outside-range preservation
and equal indexed seed images preserves any larger supplied role-value image.
This also applies when the original image was established by the grown-role
theorem; its assumptions and the equality are supplied explicitly here. -/
theorem reallocated_role_value_image {n : ℕ} {ι : Type*} [Fintype ι]
    (cells : ι → Cell n) (roles : Finset (Cell n)) (values : Finset ℕ)
    (grown reallocated : Cell n ≃ Fin (n * n))
    (hsub : Finset.univ.image cells ⊆ roles)
    (hfixed : ∀ c, c ∉ Set.range cells → entry reallocated c = entry grown c)
    (hseed : Finset.univ.image (fun x => entry reallocated (cells x)) =
      Finset.univ.image (fun x => entry grown (cells x)))
    (hvalues : roles.image (entry grown) = values) :
    roles.image (entry reallocated) = values := by
  classical
  have hs : (Finset.univ.image cells).image (entry reallocated) =
      (Finset.univ.image cells).image (entry grown) := by
    simpa [Finset.image_image, Function.comp_def] using hseed
  have hf : ∀ c ∈ roles, c ∉ Finset.univ.image cells → entry reallocated c = entry grown c := by
    intro c _ hc
    apply hfixed
    intro ⟨x, hx⟩
    apply hc
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  exact (role_value_image_preserved roles (Finset.univ.image cells) (entry grown) (entry reallocated)
    hsub hf hs).trans hvalues

/-- The existing within-stage seed permutation preserves the value image of
the actual early-and-growth roles. A known grown-square image can therefore be
carried to the reallocated square, without assumptions about other operations. -/
theorem fw_seed_reallocation_preserves_role_value_image {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (grown b : Cell n ≃ Fin (n * n)) (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8))))
    (hfixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c)
    (hperm : ∀ j i side, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, i), side)) =
      entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, ω j i), side)))
    (values : Finset ℕ)
    (hvalues : (fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)).image (entry grown) = values) :
    (fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)).image (entry b) = values := by
  classical
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  have hsub : Finset.univ.image cells ⊆ roles := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_union_left _
      (fw_seed_existing_cells_mem_early hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc x)
  have hseedImage : Finset.univ.image (fun x => entry b (cells x)) =
      Finset.univ.image (fun x => entry grown (cells x)) := by
    have hfun : (fun x => entry b (cells x)) =
        (fun x => entry grown (cells x)) ∘ stagePairPermutation ω := by
      funext ⟨⟨j, i⟩, side⟩
      exact hperm j i side
    rw [hfun, ← Finset.image_image, Finset.image_univ_of_surjective (stagePairPermutation ω).surjective]
  exact reallocated_role_value_image cells roles values grown b hsub hfixed hseedImage hvalues

end
end Sude
