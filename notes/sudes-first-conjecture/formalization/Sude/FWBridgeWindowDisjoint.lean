import Sude.FWBridgeStocks
import Sude.BridgeDepletion

/-! Exact same-side separation of FW's five nominal source windows. -/
namespace Sude
noncomputable section

/-- The capped span scales from the normalized FW radius for positive X. -/
theorem fw_bridge_nominal_span_scale (X : ℝ) (hX : 0 < X) (j : ℕ) :
    bridgeSpan X (fwBridgeRadius X j) = min (fwBridgeRatio j) (1 / 2) * X := by
  rw [min_mul_of_nonneg _ _ (le_of_lt hX)]
  simp only [bridgeSpan, fwBridgeRadius]
  congr 1 <;> ring

/-- The five FW source windows are strictly separated on each same side.
In particular the last window uses the capped `1/2` span, not its larger
accumulated nominal coverage. -/
theorem fw_bridge_nominal_windows_ordered (X : ℝ) (hX : 0 < X)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) (hij : i < j) :
    fwBridgeLowEnd X (fwBridgeRadius X j) < fwBridgeLowStart X (fwBridgeRadius X i) ∧
    fwBridgeHighEnd X (fwBridgeRadius X i) < fwBridgeHighStart X (fwBridgeRadius X j) := by
  have hsi := fw_bridge_nominal_span_scale X hX i
  have hsj := fw_bridge_nominal_span_scale X hX j
  simp only [fwBridgeLowEnd, fwBridgeLowStart, fwBridgeHighEnd, fwBridgeHighStart,
    fwBridgeWidth]
  rw [hsi, hsj]
  constructor <;> interval_cases i <;> interval_cases j <;> norm_num [fwBridgeRatio] at * <;> nlinarith

/-- The nominal stage radii themselves are positive for positive X. -/
theorem fw_bridge_nominal_radius_pos (X : ℝ) (hX : 0 < X) (i : ℕ) (hi : i < 5) :
    0 < fwBridgeRadius X i := by
  exact mul_pos ((fw_bridge_five_stage_schedule.2.2.2.2.2.2.1 i hi).1) hX

/-- The two distinct-stage low stocks are disjoint. This is a geometric
fact about the source windows and asserts no positive prime count. -/
theorem fw_bridge_nominal_low_stocks_disjoint (X : ℝ) (hX : 0 < X)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) (hne : i ≠ j) :
    Disjoint (fwBridgeLowStock X (fwBridgeRadius X i))
      (fwBridgeLowStock X (fwBridgeRadius X j)) := by
  have hforward : ∀ u < 5, ∀ v < 5, u < v →
      Disjoint (fwBridgeLowStock X (fwBridgeRadius X u))
        (fwBridgeLowStock X (fwBridgeRadius X v)) := by
    intro u hu v hv huv
    have hgu := fw_bridge_window_geometry X (fwBridgeRadius X u) hX
      (fw_bridge_nominal_radius_pos X hX u hu)
    have hgv := fw_bridge_window_geometry X (fwBridgeRadius X v) hX
      (fw_bridge_nominal_radius_pos X hX v hv)
    have horder := (fw_bridge_nominal_windows_ordered X hX u v hu hv huv).1
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_apInterval_iff _ _ 2 1 (by linarith [hgu.2.2.1])
      (by linarith [hgu.2.2.1, hgu.2.2.2.1]) p).mp hp
    have hq' := (mem_apInterval_iff _ _ 2 1 (by linarith [hgv.2.2.1])
      (by linarith [hgv.2.2.1, hgv.2.2.2.1]) p).mp hq
    linarith [hp'.2.1, hq'.2.2.1]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hforward i hi j hj hlt
  · exact (hforward j hj i hi hgt).symm

/-- The two distinct-stage high stocks are disjoint. -/
theorem fw_bridge_nominal_high_stocks_disjoint (X : ℝ) (hX : 0 < X)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) (hne : i ≠ j) :
    Disjoint (fwBridgeHighStock X (fwBridgeRadius X i))
      (fwBridgeHighStock X (fwBridgeRadius X j)) := by
  have hforward : ∀ u < 5, ∀ v < 5, u < v →
      Disjoint (fwBridgeHighStock X (fwBridgeRadius X u))
        (fwBridgeHighStock X (fwBridgeRadius X v)) := by
    intro u hu v hv huv
    have hgu := fw_bridge_window_geometry X (fwBridgeRadius X u) hX
      (fw_bridge_nominal_radius_pos X hX u hu)
    have hgv := fw_bridge_window_geometry X (fwBridgeRadius X v) hX
      (fw_bridge_nominal_radius_pos X hX v hv)
    have horder := (fw_bridge_nominal_windows_ordered X hX u v hu hv huv).2
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_apInterval_iff _ _ 2 1
      (by linarith [hgu.2.2.1, hgu.2.2.2.1, hgu.2.2.2.2.1])
      (by linarith [hgu.2.2.1, hgu.2.2.2.1, hgu.2.2.2.2.1, hgu.2.2.2.2.2.1]) p).mp hp
    have hq' := (mem_apInterval_iff _ _ 2 1
      (by linarith [hgv.2.2.1, hgv.2.2.2.1, hgv.2.2.2.2.1])
      (by linarith [hgv.2.2.1, hgv.2.2.2.1, hgv.2.2.2.2.1, hgv.2.2.2.2.2.1]) p).mp hq
    linarith [hp'.2.2.1, hq'.2.1]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hforward i hi j hj hlt
  · exact (hforward j hj i hi hgt).symm

/-- Any low-stock overlap index is the stage itself. Self-overlap is not
asserted without a nonempty-stock hypothesis. -/
theorem fw_bridge_nominal_low_overlap_subset (X : ℝ) (hX : 0 < X) (j : ℕ) (hj : j < 5) :
    overlappingBridgeWindows (Finset.range 5) (fun i => fwBridgeLowStock X (fwBridgeRadius X i))
      (fwBridgeLowStock X (fwBridgeRadius X j)) ⊆ {j} := by
  intro i hi
  have h := (Finset.mem_filter.mp hi)
  have hne : i = j := by
    by_contra hne
    exact h.2 (fw_bridge_nominal_low_stocks_disjoint X hX i j (Finset.mem_range.mp h.1) hj hne)
  simpa [hne]

/-- The corresponding high-stock overlap index is also confined to itself. -/
theorem fw_bridge_nominal_high_overlap_subset (X : ℝ) (hX : 0 < X) (j : ℕ) (hj : j < 5) :
    overlappingBridgeWindows (Finset.range 5) (fun i => fwBridgeHighStock X (fwBridgeRadius X i))
      (fwBridgeHighStock X (fwBridgeRadius X j)) ⊆ {j} := by
  intro i hi
  have h := (Finset.mem_filter.mp hi)
  have hne : i = j := by
    by_contra hne
    exact h.2 (fw_bridge_nominal_high_stocks_disjoint X hX i j (Finset.mem_range.mp h.1) hj hne)
  simpa [hne]


/-- For the actual real half-open low windows, the only overlapping stage
is itself, exactly matching the source's `overlap_indices=[j]`. -/
theorem fw_bridge_nominal_low_window_overlap_iff (X : ℝ) (hX : 0 < X)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    (∃ x : ℝ, x ∈ Set.Ioc (fwBridgeLowStart X (fwBridgeRadius X i))
        (fwBridgeLowEnd X (fwBridgeRadius X i)) ∧
      x ∈ Set.Ioc (fwBridgeLowStart X (fwBridgeRadius X j))
        (fwBridgeLowEnd X (fwBridgeRadius X j))) ↔ i = j := by
  constructor
  · rintro ⟨x, hxi, hxj⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := (fw_bridge_nominal_windows_ordered X hX i j hi hj hlt).1
      exact (not_lt_of_ge (le_trans hxj.2 h.le)) hxi.1
    · have h := (fw_bridge_nominal_windows_ordered X hX j i hj hi hgt).1
      exact (not_lt_of_ge (le_trans hxi.2 h.le)) hxj.1
  · intro heq
    subst i
    have h := fw_bridge_window_geometry X (fwBridgeRadius X j) hX
      (fw_bridge_nominal_radius_pos X hX j hj)
    let x := (fwBridgeLowStart X (fwBridgeRadius X j) + fwBridgeLowEnd X (fwBridgeRadius X j)) / 2
    have hx : x ∈ Set.Ioc (fwBridgeLowStart X (fwBridgeRadius X j))
        (fwBridgeLowEnd X (fwBridgeRadius X j)) := by
      dsimp [x]
      exact ⟨by linarith [h.2.2.2.1], by linarith [h.2.2.2.1]⟩
    exact ⟨x, hx, hx⟩

/-- The same exact overlap statement holds for the reflected high windows. -/
theorem fw_bridge_nominal_high_window_overlap_iff (X : ℝ) (hX : 0 < X)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    (∃ x : ℝ, x ∈ Set.Ioc (fwBridgeHighStart X (fwBridgeRadius X i))
        (fwBridgeHighEnd X (fwBridgeRadius X i)) ∧
      x ∈ Set.Ioc (fwBridgeHighStart X (fwBridgeRadius X j))
        (fwBridgeHighEnd X (fwBridgeRadius X j))) ↔ i = j := by
  constructor
  · rintro ⟨x, hxi, hxj⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := (fw_bridge_nominal_windows_ordered X hX i j hi hj hlt).2
      exact (not_lt_of_ge (le_trans hxi.2 h.le)) hxj.1
    · have h := (fw_bridge_nominal_windows_ordered X hX j i hj hi hgt).2
      exact (not_lt_of_ge (le_trans hxj.2 h.le)) hxi.1
  · intro heq
    subst i
    have h := fw_bridge_window_geometry X (fwBridgeRadius X j) hX
      (fw_bridge_nominal_radius_pos X hX j hj)
    let x := (fwBridgeHighStart X (fwBridgeRadius X j) + fwBridgeHighEnd X (fwBridgeRadius X j)) / 2
    have hx : x ∈ Set.Ioc (fwBridgeHighStart X (fwBridgeRadius X j))
        (fwBridgeHighEnd X (fwBridgeRadius X j)) := by
      dsimp [x]
      exact ⟨by linarith [h.2.2.2.2.2.1], by linarith [h.2.2.2.2.2.1]⟩
    exact ⟨x, hx, hx⟩

end
end Sude
