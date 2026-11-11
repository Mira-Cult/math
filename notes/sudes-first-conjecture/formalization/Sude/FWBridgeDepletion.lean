import Sude.FWBridgeWindowDisjoint

/-! Exact prior-depletion accounting for the nominal source-width FW bridge. -/
namespace Sude
noncomputable section

/-- An FW low stock is disjoint from every FW high stock, including stocks
from different stages. Only source-window geometry is used. -/
theorem fw_bridge_low_high_stocks_disjoint (X R S : ℝ) (hX : 0 < X)
    (hR : 0 < R) (hS : 0 < S) :
    Disjoint (fwBridgeLowStock X R) (fwBridgeHighStock X S) := by
  have hl := fw_bridge_window_geometry X R hX hR
  have hh := fw_bridge_window_geometry X S hX hS
  have hsl := bridgeSpan_properties X R hX hR
  have hsh := bridgeSpan_properties X S hX hS
  have hlow : fwBridgeLowEnd X R < X / 2 := by
    simp only [fwBridgeLowEnd, fwBridgeLowStart, fwBridgeWidth]
    linarith [hsl.1]
  have hhigh : X / 2 < fwBridgeHighStart X S := by
    simp only [fwBridgeHighStart, fwBridgeHighEnd, fwBridgeWidth]
    linarith [hsh.1]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_apInterval_iff _ _ 2 1 (by linarith [hl.2.2.1])
    (by linarith [hl.2.2.1, hl.2.2.2.1]) p).mp hp
  have hq' := (mem_apInterval_iff _ _ 2 1
    (by linarith [hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1])
    (by linarith [hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1]) p).mp hq
  linarith [hp'.2.2.1, hq'.2.1]

/-- At a nominal stage, all earlier supplied valid batches are disjoint from
both current stocks. This assumes validity of the earlier blocks; it neither
constructs them nor proves their stock or physical-placement hypotheses. -/
theorem fw_nominal_prior_batches_disjoint_current (X : ℝ) (hX : 0 < X)
    (batches : ℕ → List DoublePair) (j : ℕ) (hj : j < 5)
    (hvalid : ∀ i < j, ∀ b ∈ batches i,
      b.valid (fwBridgeLowStock X (fwBridgeRadius X i))
        (fwBridgeHighStock X (fwBridgeRadius X i))) :
    Disjoint (priorBridgeReservation ∅ (Finset.range j) batches)
      (fwBridgeLowStock X (fwBridgeRadius X j)) ∧
    Disjoint (priorBridgeReservation ∅ (Finset.range j) batches)
      (fwBridgeHighStock X (fwBridgeRadius X j)) := by
  have hmem : ∀ p ∈ priorBridgeReservation ∅ (Finset.range j) batches,
      ∃ i < j, p ∈ doubleBatchLow (batches i) ∨ p ∈ doubleBatchHigh (batches i) := by
    intro p hp
    simp only [priorBridgeReservation, stagedReservation, Finset.empty_union,
      Finset.mem_biUnion, Finset.mem_range] at hp
    simpa only [Finset.mem_union] using hp
  have hcurrent : 0 < fwBridgeRadius X j := fw_bridge_nominal_radius_pos X hX j hj
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp htarget
    obtain ⟨i, hi, hside⟩ := hmem p hp
    have hi5 : i < 5 := by omega
    have hvalidi := hvalid i hi
    have hprior : 0 < fwBridgeRadius X i := fw_bridge_nominal_radius_pos X hX i hi5
    rcases hside with hl | hh
    · have hpLow := doubleBatchLow_subset (batches i) _ _ hvalidi hl
      exact Finset.disjoint_left.mp
        (fw_bridge_nominal_low_stocks_disjoint X hX i j hi5 hj (by omega)) hpLow htarget
    · have hpHigh := doubleBatchHigh_subset (batches i) _ _ hvalidi hh
      exact Finset.disjoint_left.mp
        (fw_bridge_low_high_stocks_disjoint X _ _ hX hcurrent hprior) htarget hpHigh
  · apply Finset.disjoint_left.mpr
    intro p hp htarget
    obtain ⟨i, hi, hside⟩ := hmem p hp
    have hi5 : i < 5 := by omega
    have hvalidi := hvalid i hi
    have hprior : 0 < fwBridgeRadius X i := fw_bridge_nominal_radius_pos X hX i hi5
    rcases hside with hl | hh
    · have hpLow := doubleBatchLow_subset (batches i) _ _ hvalidi hl
      exact Finset.disjoint_left.mp
        (fw_bridge_low_high_stocks_disjoint X _ _ hX hprior hcurrent) hpLow htarget
    · have hpHigh := doubleBatchHigh_subset (batches i) _ _ hvalidi hh
      exact Finset.disjoint_left.mp
        (fw_bridge_nominal_high_stocks_disjoint X hX i j hi5 hj (by omega)) hpHigh htarget

/-- Earlier nominal FW batches add no deletion to either current side:
intersecting the full reservation with a side gives exactly the initial
reservation's intersection. No assumption about prime counts is made. -/
theorem fw_nominal_prior_reservation_intersections (X : ℝ) (hX : 0 < X)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair) (j : ℕ) (hj : j < 5)
    (hvalid : ∀ i < j, ∀ b ∈ batches i,
      b.valid (fwBridgeLowStock X (fwBridgeRadius X i))
        (fwBridgeHighStock X (fwBridgeRadius X i))) :
    let reserved := priorBridgeReservation initial (Finset.range j) batches
    reserved ∩ fwBridgeLowStock X (fwBridgeRadius X j) =
      initial ∩ fwBridgeLowStock X (fwBridgeRadius X j) ∧
    reserved ∩ fwBridgeHighStock X (fwBridgeRadius X j) =
      initial ∩ fwBridgeHighStock X (fwBridgeRadius X j) := by
  have hd := fw_nominal_prior_batches_disjoint_current X hX batches j hj hvalid
  have hreserve : priorBridgeReservation initial (Finset.range j) batches =
      initial ∪ priorBridgeReservation ∅ (Finset.range j) batches := by
    simp [priorBridgeReservation, stagedReservation]
  rw [hreserve]
  constructor
  · ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hstock⟩
      · exact ⟨hp, hstock⟩
      · exact False.elim (Finset.disjoint_left.mp hd.1 hp hstock)
    · rintro ⟨hp, hstock⟩
      exact ⟨Or.inl hp, hstock⟩
  · ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hstock⟩
      · exact ⟨hp, hstock⟩
      · exact False.elim (Finset.disjoint_left.mp hd.2 hp hstock)
    · rintro ⟨hp, hstock⟩
      exact ⟨Or.inl hp, hstock⟩

end
end Sude
