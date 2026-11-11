import Sude.StagePairReallocation
import Sude.FWGrowthEarlyGeometry
import Sude.BTGrowingOffsetPhysical

/-! Reallocation of the retained seed endpoints already installed in FW's
offset rectangles and two ordinary layer families. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- The actual FW seed roles, reindexed by stage, pair and endpoint. -/
def fwSeedExistingPairCells {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) : (Fin 16 × Fin (6 * (n + 8))) × Bool → Cell n :=
  fun x => btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
    ((Equiv.ofBijective (prefixPhysicalInput (P := 16)
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)) (fwSeedPhysicalInput_bijective n)).symm x)

/-- Starting with the exact FW seed placement and its preserved early roles,
any supplied within-stage permutation reallocates the same already-installed
retained pairs. All cells outside the seed role image remain fixed; the
per-stage and total retained endpoint sets and each gap 2 are preserved.
The seed support includes diagonal cells: no diagonal-sum or line-balance
preservation is asserted. -/
theorem fw_reallocate_existing_retained_seed_pairs {n L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry old (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ j i side, entry b (cells ((j, i), side)) = entry grown (cells ((j, ω j i), side))) ∧
      (∀ c, c ∉ Set.range cells → entry b c = entry grown c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
        entry b (cells ((j, x.1), x.2))) =
        Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
        entry grown (cells ((j, x.1), x.2)))) ∧
      Finset.univ.image (fun x => entry b (cells x)) =
        retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub ∧
      (∀ j i, entry b (cells ((j, i), true)) = entry b (cells ((j, i), false)) + 2) := by
  classical
  dsimp only
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16) hfit hdiag) (fwSeedPhysicalInput_bijective n)
  let role := btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  have hrole_fixed : ∀ x, entry grown (role x) = entry old (role x) := by
    intro x
    apply hfixed
    cases x with
    | inl x =>
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    | inr x =>
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by cases x <;> rfl⟩
  have hplace : ∀ x, entry grown (role x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixPhysicalInput hfit hdiag x)) := by
    intro x
    rw [hrole_fixed x]
    cases x with
    | inl x => exact hsd x
    | inr x => cases x <;> first | exact hso (Sum.inl _) | exact hso (Sum.inr _)
  obtain ⟨hroleinj, hroleimage⟩ := prefixPhysical_realizes_retained
    candidates 17 16 (6 * (n + 8)) 2 6 3 n hcard kept hsub hkept hinj
    hfit hdiag hexact role (entry grown) hplace
  have hc : Function.Injective cells := hroleinj.comp e.symm.injective
  have hval : ∀ x, entry grown (cells x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept x) := by
    intro x
    have hp := hplace (e.symm x)
    have he : prefixPhysicalInput hfit hdiag (e.symm x) = x := e.apply_symm_apply x
    rw [he] at hp
    exact hp
  obtain ⟨b, hb, hfixedb, hstage, hgap⟩ := reallocate_existing_stage_pairs grown cells hc ω
  refine ⟨b, hb, hfixedb, hstage, ?_, ?_⟩
  · have himage : Finset.univ.image (fun x => entry grown (cells x)) =
        retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
      simp_rw [hval]
      exact retainedSeedSlot_image candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept hinj
    have hfun : (fun x => entry b (cells x)) =
        (fun x => entry grown (cells x)) ∘ stagePairPermutation ω := by
      funext ⟨⟨j, i⟩, side⟩
      exact hb j i side
    rw [hfun, ← Finset.image_image, Finset.image_univ_of_surjective (stagePairPermutation ω).surjective]
    exact himage
  · apply hgap (fun _ => 2)
    intro j i
    rw [hval, hval]
    simp [retainedSeedSlot, sortedSeedEndpoint, pairEndpoint]

end
end Sude
