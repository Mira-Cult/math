import Sude.FWEnhancedCrossingPhysical

/-! Extend an existing labelled even grid by the actual selected wide pairs
at one fixed physical edge. No simultaneous switchability is asserted. -/
namespace Sude
noncomputable section

/-- Relabel an existing even grid on the left of a disjoint sum. -/
theorem fw_wide_relabel_grid {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (g : α → ℕ) (wide : β → ℕ) (R : ℕ)
    (hgrid : CompleteEvenGrid S g R) :
    CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩)
      (Sum.elim g wide : Sum α β → ℕ) R := by
  intro t ht heven
  obtain ⟨T, hT, hsum⟩ := hgrid t ht heven
  refine ⟨T.map ⟨Sum.inl, Sum.inl_injective⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨a, hT ha, rfl⟩
  · simpa using hsum

/-- Each fresh even wide label can be added while its gap is no larger than
    the original grid radius. -/
theorem fw_wide_family_grid {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (g : α → ℕ) (wide : β → ℕ) (R : ℕ)
    (hgrid : CompleteEvenGrid S g R) (heven : 2 ∣ R)
    (T : Finset β) (hwide : ∀ x ∈ T, 2 ∣ wide x ∧ wide x ≤ R) :
    CompleteEvenGrid
      (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ T.map ⟨Sum.inr, Sum.inr_injective⟩)
      (Sum.elim g wide : Sum α β → ℕ) (R + ∑ x ∈ T, wide x) ∧
    2 ∣ R + ∑ x ∈ T, wide x := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ⟨fw_wide_relabel_grid S g wide R hgrid, heven⟩
  | @insert x T hx ih =>
    have hwT : ∀ y ∈ T, 2 ∣ wide y ∧ wide y ≤ R := by
      intro y hy
      exact hwide y (Finset.mem_insert_of_mem hy)
    obtain ⟨hprev, heprev⟩ := ih hwT
    have hwx := hwide x (Finset.mem_insert_self x T)
    have hfresh : Sum.inr x ∉ S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        T.map ⟨Sum.inr, Sum.inr_injective⟩ := by
      simp [hx]
    have hstep := completeEvenGrid_insert
      (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ T.map ⟨Sum.inr, Sum.inr_injective⟩)
      (Sum.elim g wide : Sum α β → ℕ) (R + ∑ y ∈ T, wide y)
      (Sum.inr x) hfresh heprev hwx.1 (by simp only [Sum.elim_inr]; omega) hprev
    constructor
    · simpa [Finset.map_insert, Finset.union_insert, Finset.sum_insert, hx, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hstep
    · have he := dvd_add heprev hwx.1
      simpa [Finset.sum_insert, hx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- Add all supplied physical wide pairs at one fixed graph edge. The labels
are distinct stage indices; this result does not assert that the corresponding
physical switches can be performed simultaneously. -/
theorem fw_physical_wide_edge_grid {α : Type*} [DecidableEq α] {n L : ℕ}
    (X : ℝ) (S : Finset α) (g : α → ℕ) (R : ℕ)
    (hgrid : CompleteEvenGrid S g R) (heven : 2 ∣ R) (hcover : X ≤ R)
    (hwideRect : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n * n)) (k : Fin 3) (e : Fin n)
    (hwide : ∀ j : Fin (3 * (n / 450)), ∃ gap : ℕ,
      0 < gap ∧ 2 ∣ gap ∧
      (∀ network : Bool,
        entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
        entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + gap) ∧
      (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X) :
    ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
          entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + wide j) ∧
        (2 / 3 : ℝ) * X ≤ (wide j : ℝ) ∧ (wide j : ℝ) < X) ∧
      CompleteEvenGrid
        (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
          Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim g wide : Sum α (Fin (3 * (n / 450))) → ℕ)
        (R + ∑ j, wide j) ∧
      2 ∣ R + ∑ j, wide j ∧
      (2 : ℝ) * (n / 450 : ℕ) * X ≤ (∑ j, (wide j : ℝ)) := by
  classical
  choose wide hw using hwide
  have hbounded : ∀ j ∈ (Finset.univ : Finset (Fin (3 * (n / 450)))),
      2 ∣ wide j ∧ wide j ≤ R := by
    intro j _
    refine ⟨(hw j).2.1, ?_⟩
    have hreal : (wide j : ℝ) ≤ R := le_trans (le_of_lt (hw j).2.2.2.2) hcover
    exact_mod_cast hreal
  have hres := fw_wide_family_grid S g wide R hgrid heven Finset.univ hbounded
  have hsum : (∑ _j : Fin (3 * (n / 450)), (2 / 3 : ℝ) * X) ≤
      ∑ j, (wide j : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact (hw j).2.2.2.1
  have htotal : (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide j : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    nlinarith
  exact ⟨wide, hw, hres.1, hres.2, htotal⟩

/-- The actual trace radius plus the five selected bridge gaps is even. -/
theorem fw_physical_bridge_radius_even {n Q : ℕ}
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (edge : Fin 3 × Fin n) :
    2 ∣ last + ∑ j ∈ Finset.range 5,
      selectedBridgeGap batches (bridgeOrdinaryBlockIndex (r := 3) (d := 6)
        (k := 3 * (n + 8)) (by omega) edge) j := by
  have hlast : 2 ∣ last := (fw_even_trace_radius_lower trace).2
  have hsum : 2 ∣ ∑ j ∈ Finset.range 5,
      selectedBridgeGap batches (bridgeOrdinaryBlockIndex (r := 3) (d := 6)
        (k := 3 * (n + 8)) (by omega) edge) j := by
    apply Finset.dvd_sum
    intro j hj
    exact (fw_selected_bridge_gap_bounds n ∅ batches hvalid _ j (Finset.mem_range.mp hj)).1
  exact dvd_add hlast hsum

/-- Given the per-edge bridge grid and wide-role equations exported by the
same physical crossing witness, append every wide-stage label at that edge.
The graph and the physical pairs remain supplied by that witness. -/
theorem fw_physical_bridge_wide_edge_grid {α : Type*} [DecidableEq α] {n L Q : ℕ}
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (S : Finset α) (g : α → ℕ) (edge : Fin 3 × Fin n)
    (hgrid : CompleteEvenGrid S g (last + ∑ j ∈ Finset.range 5,
      selectedBridgeGap batches (bridgeOrdinaryBlockIndex (r := 3) (d := 6)
        (k := 3 * (n + 8)) (by omega) edge) j))
    (hcover : (poolMaximum n : ℝ) ≤ (last + ∑ j ∈ Finset.range 5,
      selectedBridgeGap batches (bridgeOrdinaryBlockIndex (r := 3) (d := 6)
        (k := 3 * (n + 8)) (by omega) edge) j : ℕ))
    (hwideRect : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n * n))
    (hwide : ∀ j : Fin (3 * (n / 450)), ∃ gap : ℕ,
      0 < gap ∧ gap % 2 = 0 ∧
      (∀ network : Bool,
        entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
        entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network false)) + gap) ∧
      (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) :
    let R := last + ∑ j ∈ Finset.range 5,
      selectedBridgeGap batches (bridgeOrdinaryBlockIndex (r := 3) (d := 6)
        (k := 3 * (n + 8)) (by omega) edge) j
    ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
          entry a (fwWidePhysicalCells hwideRect hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j) ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide j : ℝ) ∧ (wide j : ℝ) < poolMaximum n) ∧
      CompleteEvenGrid
        (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim g wide : Sum α (Fin (3 * (n / 450))) → ℕ)
        (R + ∑ j, wide j) ∧
      2 ∣ R + ∑ j, wide j ∧
      (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ) := by
  dsimp only
  apply fw_physical_wide_edge_grid (poolMaximum n) S g _ hgrid
    (fw_physical_bridge_radius_even trace batches hvalid edge) hcover
    hwideRect hs choice rows cols hr hc a edge.1 edge.2
  intro j
  obtain ⟨gap, hpos, heven, hpair, hlo, hhi⟩ := hwide j
  exact ⟨gap, hpos, Nat.dvd_of_mod_eq_zero heven, hpair, hlo, hhi⟩

end
end Sude
