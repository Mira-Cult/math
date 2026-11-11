import Sude.FWFourFamilyPairInjection
import Sude.FWPhysicalDoubleBlockCells

/-! Conditional simultaneous reallocation of existing bridge and wide double
blocks, keeping all seed and growth cells fixed. The supplied permutations
move gaps with source blocks; no grid or concentration claim is made. -/

namespace Sude
noncomputable section

/-- Two disjoint block families can be reallocated in succession while two
other supplied cell families remain fixed. -/
theorem fw_reallocate_two_double_families {n P W B : ℕ} {α β : Type*}
    (a : Cell n ≃ Fin (n * n))
    (bridge : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (wide : (Fin W × Fin B × Fin 2) × Bool → Cell n)
    (seed : α → Cell n) (growth : β → Cell n)
    (hb : Function.Injective bridge) (hw : Function.Injective wide)
    (hbw : ∀ x y, bridge x ≠ wide y)
    (hbs : ∀ x y, bridge x ≠ seed y) (hbg : ∀ x y, bridge x ≠ growth y)
    (hws : ∀ x y, wide x ≠ seed y) (hwg : ∀ x y, wide x ≠ growth y)
    (ωb : Fin P → Equiv.Perm (Fin B)) (τb : Fin P → Fin B → Equiv.Perm (Fin 2))
    (ωw : Fin W → Equiv.Perm (Fin B)) (τw : Fin W → Fin B → Equiv.Perm (Fin 2)) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ j b p side, entry a' (bridge ((j,b,p),side)) =
        entry a (bridge ((j,ωb j b,τb j b p),side))) ∧
      (∀ j b p side, entry a' (wide ((j,b,p),side)) =
        entry a (wide ((j,ωw j b,τw j b p),side))) ∧
      (∀ x, entry a' (seed x) = entry a (seed x)) ∧
      (∀ x, entry a' (growth x) = entry a (growth x)) ∧
      (∀ c, c ∉ Set.range bridge → c ∉ Set.range wide → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry a' (bridge ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry a (bridge ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ j, Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry a' (wide ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry a (wide ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ gap : Fin P → Fin B → ℕ, (∀ j b p,
        entry a (bridge ((j,b,p),true)) = entry a (bridge ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry a' (bridge ((j,b,p),true)) =
          entry a' (bridge ((j,b,p),false)) + gap j (ωb j b)) ∧
      (∀ gap : Fin W → Fin B → ℕ, (∀ j b p,
        entry a (wide ((j,b,p),true)) = entry a (wide ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry a' (wide ((j,b,p),true)) =
          entry a' (wide ((j,b,p),false)) + gap j (ωw j b)) := by
  obtain ⟨a1, hbentry, hbfix, hbstage, hbgap⟩ :=
    reallocate_existing_stage_double_blocks a bridge hb ωb τb
  have hwide1 (x) : entry a1 (wide x) = entry a (wide x) := by
    apply hbfix
    rintro ⟨y, hy⟩
    exact hbw y x hy
  have hseed1 (x) : entry a1 (seed x) = entry a (seed x) := by
    apply hbfix
    rintro ⟨y, hy⟩
    exact hbs y x hy
  have hgrowth1 (x) : entry a1 (growth x) = entry a (growth x) := by
    apply hbfix
    rintro ⟨y, hy⟩
    exact hbg y x hy
  obtain ⟨a2, hwentry, hwfix, hwstage, hwgap⟩ :=
    reallocate_existing_stage_double_blocks a1 wide hw ωw τw
  have hbridge2 (x) : entry a2 (bridge x) = entry a1 (bridge x) := by
    apply hwfix
    rintro ⟨y, hy⟩
    exact hbw x y hy.symm
  have hseed2 (x) : entry a2 (seed x) = entry a (seed x) := by
    rw [hwfix (seed x) (by rintro ⟨y,hy⟩; exact hws y x hy), hseed1]
  have hgrowth2 (x) : entry a2 (growth x) = entry a (growth x) := by
    rw [hwfix (growth x) (by rintro ⟨y,hy⟩; exact hwg y x hy), hgrowth1]
  refine ⟨a2, ?_, ?_, hseed2, hgrowth2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j b p side
    rw [hbridge2, hbentry]
  · intro j b p side
    rw [hwentry, hwide1]
  · intro c hbr hwide
    rw [hwfix c hwide, hbfix c hbr]
  · intro j
    have h := hbstage j
    simpa only [hbridge2] using h
  · intro j
    have h := hwstage j
    simpa only [hwide1] using h
  · intro gap hgap j b p
    simpa only [hbridge2] using hbgap gap hgap j b p
  · intro gap hgap j b p
    have hgap1 : ∀ j b p, entry a1 (wide ((j,b,p),true)) =
        entry a1 (wide ((j,b,p),false)) + gap j b := by
      simpa only [hwide1] using hgap
    exact hwgap gap hgap1 j b p


/-- Under the actual normalized four-family packing, simultaneously permute
bridge and wide double blocks while keeping every seed and growth cell fixed. -/
theorem fw_reallocate_bridge_wide_double_blocks {n P : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n))
    (ωb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (τb : Fin 5 → Fin (3 * (n + 8)) → Equiv.Perm (Fin 2))
    (ωw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (τw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Equiv.Perm (Fin 2)) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ j b p side, entry a' (bridge ((j,b,p),side)) =
        entry a (bridge ((j,ωb j b,τb j b p),side))) ∧
      (∀ j b p side, entry a' (wide ((j,b,p),side)) =
        entry a (wide ((j,ωw j b,τw j b p),side))) ∧
      (∀ x, entry a' (seed x) = entry a (seed x)) ∧
      (∀ x, entry a' (growth x) = entry a (growth x)) ∧
      (∀ c, c ∉ Set.range bridge → c ∉ Set.range wide → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry a' (bridge ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry a (bridge ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ j, Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry a' (wide ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry a (wide ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ gap : Fin 5 → Fin (3 * (n + 8)) → ℕ, (∀ j b p,
        entry a (bridge ((j,b,p),true)) = entry a (bridge ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry a' (bridge ((j,b,p),true)) =
          entry a' (bridge ((j,b,p),false)) + gap j (ωb j b)) ∧
      (∀ gap : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → ℕ, (∀ j b p,
        entry a (wide ((j,b,p),true)) = entry a (wide ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry a' (wide ((j,b,p),true)) =
          entry a' (wide ((j,b,p),false)) + gap j (ωw j b)) := by
  dsimp only
  obtain ⟨hfamily, _⟩ := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  change Function.Injective cells at hfamily
  have hb : Function.Injective (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
        cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n y)))) from h)
    exact (fwBlockPairIndex 5 n).injective (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj he)))
  have hw : Function.Injective (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
        cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n y))) from h)
    exact (fwBlockPairIndex (3 * (n / 450)) n).injective (Sum.inr.inj (Sum.inl.inj he))
  have hbw : ∀ x y, fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x ≠
      fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hbs : ∀ x y, fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x ≠
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inl (Sum.inl (Sum.inr y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hbg : ∀ x y, fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x ≠
      btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  have hws : ∀ x y, fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x ≠
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
      cells (Sum.inl (Sum.inl (Sum.inr y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hwg : ∀ x y, fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x ≠
      btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
      cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  exact fw_reallocate_two_double_families a _ _ _ _ hb hw hbw hbs hbg hws hwg ωb τb ωw τw

end
end Sude
