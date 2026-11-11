import Sude.FWSeedOffsetActualDiagonal
import Sude.ActiveRectangleDiagonalGeometry
import Sude.FWSelectedThetaWitness

/-! Exact reindexing of designated seed rectangle diagonals by physical pair
endpoints. No concentration, value bound, spare-cell or CY claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- The twelve seed rectangle slots on the chosen physical diagonal. -/
def fwSeedPhysicalSideRect (side : Bool) (r : Fin 12) : Fin (4*6) :=
  ⟨(if side then 0 else 12) + r.val, by cases side <;> simp <;> have := r.isLt <;> omega⟩

/-- Their actual rectangle labels, with a separate index for each seed stage. -/
def fwSeedPhysicalSideLabel {L : ℕ} (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (side : Bool) (x : Fin 16 × Fin 12) : Fin L :=
  fwSeedRectangle hseed (finProdFinEquiv (x.1, fwSeedPhysicalSideRect side x.2))

theorem fw_seed_physical_side_label_injective {L : ℕ} (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (side : Bool) : Function.Injective (fwSeedPhysicalSideLabel hseed side) := by
  intro x y h
  have hp := finProdFinEquiv.injective ((fwSeedRectangle_injective hseed) h)
  have hj : x.1 = y.1 := congrArg (fun q : Fin 16 × Fin (4*6) => q.1) hp
  have hr := congrArg (fun q => q.2.val) hp
  apply Prod.ext hj
  apply Fin.ext
  cases side <;> simp [fwSeedPhysicalSideRect] at hr <;> omega

/-- The designated side corner is exactly the false endpoint of pair zero. -/
theorem fw_seed_physical_side_corner_eq_pair {n L : ℕ}
    (hseed : 5*(4*6)+16*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (side : Bool) (x : Fin 16 × Fin 12) :
    packedRectangleCorner hs choice (fwSeedPhysicalSideLabel hseed side x, 0) =
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
        ((x.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega)
          (fwSeedPhysicalSideRect side x.2, 0)), false) := by
  simpa [fwSeedPhysicalSideLabel, prefixPairCorner] using
    (fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc x.1
      (fwSeedPhysicalSideRect side x.2) 0 false).symm

/-- All and only the actual seed rectangle labels. -/
def fwSeedPhysicalLabels {L : ℕ} (hseed : 5*(4*6)+16*(4*6) ≤ L) : Finset (Fin L) :=
  (Finset.univ : Finset (Fin 16 × Fin (4*6))).image
    (fun x => fwSeedRectangle hseed (finProdFinEquiv x))

theorem fw_seed_physical_labels_eq_image {L : ℕ} (hseed : 5*(4*6)+16*(4*6) ≤ L) :
    fwSeedPhysicalLabels hseed = (Finset.univ : Finset (Fin (16*(4*6)))).image (fwSeedRectangle hseed) := by
  classical
  ext z
  simp only [fwSeedPhysicalLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨finProdFinEquiv x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨finProdFinEquiv.symm x, by simpa using hx⟩

/-- The actual selected theta choice supplies the generic side pattern. -/
theorem fw_selected_seed_physical_side_choice {n : ℕ} (hnlo : 19485 ≤ n)
    (hseed : 5*(4*6)+16*(4*6) ≤ fwJointRectangleCount n 254)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (j : Fin 16) (r : Fin (4*6)) :
    fwSelectedThetaChoice hnlo otherChoice (fwSeedRectangle hseed (finProdFinEquiv (j,r))) =
      decide (r.val < 12) := by
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  have h := fwBridgeSeedWideGrowthChoice_seed hrect hseed hwide hmax otherChoice j r
  simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
    fwBridgeSeedWideRectangleChoice, hrect, hwide, hmax] using h

theorem fw_seed_physical_side_labels {L : ℕ} (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (choice : Fin L → Bool)
    (hchoice : ∀ (j : Fin 16) (r : Fin (4*6)),
      choice (fwSeedRectangle hseed (finProdFinEquiv (j,r))) = decide (r.val < 12))
    (side : Bool) :
    (fwSeedPhysicalLabels hseed).filter (fun i => choice i = side) =
      (Finset.univ : Finset (Fin 16 × Fin 12)).image (fwSeedPhysicalSideLabel hseed side) := by
  classical
  ext z
  simp only [fwSeedPhysicalLabels, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨j,r⟩, hr⟩, hc⟩
    have hc' : decide (r.val < 12) = side := by rw [← hchoice j r, hr]; exact hc
    cases side with
    | false =>
      have hrv : 12 ≤ r.val := by simpa using hc'
      let x : Fin 16 × Fin 12 := (j, ⟨r.val - 12, by have h := r.isLt; omega⟩)
      refine ⟨x, ?_⟩
      rw [← hr]
      apply congrArg (fwSeedRectangle hseed)
      apply congrArg finProdFinEquiv
      dsimp [fwSeedPhysicalSideLabel, fwSeedPhysicalSideRect, x]
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change 12 + (r.val - 12) = r.val
        omega
    | true =>
      have hrv : r.val < 12 := by simpa using hc'
      let x : Fin 16 × Fin 12 := (j, ⟨r.val, hrv⟩)
      refine ⟨x, ?_⟩
      rw [← hr]
      apply congrArg (fwSeedRectangle hseed)
      apply congrArg finProdFinEquiv
      dsimp [fwSeedPhysicalSideLabel, fwSeedPhysicalSideRect, x]
      congr 1
      apply Fin.ext
      simp
  · rintro ⟨⟨j,r⟩, hr⟩
    let rect : Fin (4*6) := fwSeedPhysicalSideRect side r
    refine ⟨⟨(j,rect), ?_⟩, ?_⟩
    · simpa [fwSeedPhysicalSideLabel, rect] using hr
    · rw [← hr]
      change choice (fwSeedRectangle hseed (finProdFinEquiv (j,rect))) = side
      rw [hchoice]
      cases side <;> simp [rect, fwSeedPhysicalSideRect]

/-- The seed rectangle support meets each diagonal in exactly its twelve
physical pair-zero false endpoints per stage. -/
theorem fw_seed_physical_diagonal_cells {n L : ℕ}
    (hseed : 5*(4*6)+16*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool)
    (hchoice : ∀ (j : Fin 16) (r : Fin (4*6)),
      choice (fwSeedRectangle hseed (finProdFinEquiv (j,r))) = decide (r.val < 12))
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16*3) (hsc : sc.length = 16*3) :
    (∀ side : Bool,
      activeRectangleSupport hs choice (fwSeedPhysicalLabels hseed) ∩
          (if side then mainCells n else antiCells n) =
        (Finset.univ : Finset (Fin 16 × Fin 12)).image
          (fun x => fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
            ((x.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega)
              (fwSeedPhysicalSideRect side x.2, 0)), false))) := by
  classical
  intro side
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [active_rectangle_anti_cells hs hL choice,
      fw_seed_physical_side_labels hseed choice hchoice false, Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact fw_seed_physical_side_corner_eq_pair hseed hs choice sr sc hsr hsc false x
  | true =>
    simp only [↓reduceIte]
    rw [active_rectangle_main_cells hs hL choice,
      fw_seed_physical_side_labels hseed choice hchoice true, Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact fw_seed_physical_side_corner_eq_pair hseed hs choice sr sc hsr hsc true x

/-- The sum over the physical seed rectangle diagonal equals the sum over
its selected stage/slot endpoints, without duplicate corners. -/
theorem fw_seed_physical_diagonal_sum {n L : ℕ}
    (hseed : 5*(4*6)+16*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool)
    (hchoice : ∀ (j : Fin 16) (r : Fin (4*6)),
      choice (fwSeedRectangle hseed (finProdFinEquiv (j,r))) = decide (r.val < 12))
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (a : Cell n ≃ Fin (n*n)) (side : Bool) :
    (∑ z ∈ activeRectangleSupport hs choice (fwSeedPhysicalLabels hseed) ∩
        (if side then mainCells n else antiCells n), (entry a z : ℝ)) =
      ∑ j : Fin 16, ∑ r : Fin 12, (entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
        ((j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega)
          (fwSeedPhysicalSideRect side r, 0)), false)) : ℝ) := by
  classical
  let cell := fun x : Fin 16 × Fin 12 => fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    ((x.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega)
      (fwSeedPhysicalSideRect side x.2, 0)), false)
  have hinj : Function.Injective cell := by
    intro x y h
    apply fw_seed_physical_side_label_injective hseed side
    have hc : packedRectangleCorner hs choice (fwSeedPhysicalSideLabel hseed side x, 0) =
        packedRectangleCorner hs choice (fwSeedPhysicalSideLabel hseed side y, 0) := by
      rw [fw_seed_physical_side_corner_eq_pair, fw_seed_physical_side_corner_eq_pair]
      exact h
    exact congrArg Prod.fst (packedRectangleCorner_injective hs choice hc)
  rw [fw_seed_physical_diagonal_cells hseed hs hL choice hchoice sr sc hsr hsc side]
  change (∑ z ∈ Finset.univ.image cell, (entry a z : ℝ)) = _
  rw [Finset.sum_image (fun x _ y _ h => hinj h), Fintype.sum_prod_type]

end
end Sude
