import Sude.FWAffineWheelThreshold
import Sude.FWAffineWheelNeighbors
import Sude.FWWheelPairSupply

namespace Sude

/-- AW3 cancellation and candidate budget for arbitrary real cardinalities.
The strict short-pair bound is essential and is supplied independently. -/
theorem affine_pair_population_real
    {N M Mf R X r eta c₀ rho g C D P short Z : ℝ}
    (hR : 0 < R) (hX : 0 < X) (hr : 0 < r) (hg : 0 < g) (hrho : 0 < rho)
    (heta : 0 ≤ eta) (heps : 0 ≤ c₀ - eta)
    (hMf : 0 ≤ Mf) (hM : Mf ≤ M) (hN : M ≤ N)
    (hD : D = (g / rho) * (eta * M * R / (r * X) - (1 / 2 + C)))
    (hpairs : c₀ * N^2 * R / (r * X) - N / 2 ≤ P)
    (hshort : short < N * (rho * D / g + C))
    (hquota : 2 * Z * r * X ≤ (c₀ - eta) * Mf^2 * g) :
    2 * Z * R / g < P - short := by
  have hM0 : 0 ≤ M := hMf.trans hM
  have hN0 : 0 ≤ N := hM0.trans hN
  have hsq : Mf ^ 2 ≤ N ^ 2 := by nlinarith
  have hNdiff : 0 ≤ eta * N * (N - M) := by positivity
  have hepssq := mul_le_mul_of_nonneg_left hsq heps
  have hfactor : (c₀ - eta) * Mf ^ 2 ≤ c₀ * N ^ 2 - eta * M * N := by nlinarith
  have hscale : 0 ≤ R / (r * X) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hfactor hscale
  have hbudget : 2 * Z * R / g ≤ (c₀ - eta) * Mf ^ 2 * (R / (r * X)) := by
    have hfac : 0 ≤ R / (g * (r * X)) := by positivity
    have hb := mul_le_mul_of_nonneg_right hquota hfac
    have hleft : (2 * Z * r * X) * (R / (g * (r * X))) = 2 * Z * R / g := by
      field_simp
    have hright : ((c₀ - eta) * Mf ^ 2 * g) * (R / (g * (r * X))) =
        (c₀ - eta) * Mf ^ 2 * (R / (r * X)) := by
      field_simp
    rw [hleft, hright] at hb
    exact hb
  have hcancel : rho * D / g + C = eta * M * R / (r * X) - 1 / 2 := by
    rw [hD]
    field_simp
    ring
  rw [hcancel] at hshort
  have hid : (c₀ * N ^ 2 - eta * M * N) * (R / (r * X)) =
      c₀ * N ^ 2 * R / (r * X) - N * (eta * M * R / (r * X)) := by ring
  rw [hid] at hscaled
  linarith

/-- The existing upper discrepancy premise forces its allowance nonnegative. -/
theorem fw_affine_discrepancy_nonneg {W : ℕ} {rho C : ℝ}
    (hdisc : FWAffineWheelDiscrepancy W rho C) : 0 ≤ C := by
  have hc := hdisc 1 0 (by simp)
  simpa using hc


/-- Conditional FW affine-wheel candidate pair supply, using actual stock,
source threshold and the explicit real quota. -/
theorem fw_affine_common_gap_from_bins
    (S : Finset ℕ) (W R z Q : ℕ) (X L m mf eta rho C : ℝ)
    (hWodd : W % 2 = 1) (hR : 0 < R) (heven : 2 ∣ R)
    (hzQ : 0 < z * Q) (hX : 0 < X) (hL : 0 < L)
    (hbefore : (R : ℝ) ≤ X / L)
    (hS : ∀ p ∈ S, (p : ℝ) ≤ X ∧ p % 2 = 1 ∧ Nat.Coprime p W)
    (hrho : 0 < rho) (heta : 0 < eta)
    (hmf : 0 < mf) (hm : mf ≤ m) (hstock : m ≤ S.card)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (R : ℝ) - fwAffineOrigin C 1 X eta mf)
    (hslope : fwAffineSlope eta 2 m 1 X / rho ≤ 1)
    (hdisc : FWAffineWheelDiscrepancy W rho C)
    (hquota : ((z * Q : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / L)) - eta) * mf ^ 2) :
    let P := sameClassPairs S (progressionBinKey 0 R 2)
    let D := fwAffineThreshold 2 rho eta m R 1 X C
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  classical
  dsimp only
  let P := sameClassPairs S (progressionBinKey 0 R 2)
  let D := fwAffineThreshold 2 rho eta m R 1 X C
  let N : ℝ := S.card
  let c0 : ℝ := 1 / (2 * (1 + 1 / L))
  have hN : 0 < N := by dsimp [N]; linarith
  have hne : S.Nonempty := Finset.card_pos.mp (by
    have hr : (0 : ℝ) < (S.card : ℝ) := by simpa [N] using hN
    exact_mod_cast hr)
  have hNge : m ≤ N := hstock
  have heps' : 0 ≤ c0 - eta := heps
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hC : 0 ≤ C := fw_affine_discrepancy_nonneg hdisc
  have hD : 0 < D := (fw_affine_threshold_bounds (g := 2) (rho := rho) (eta := eta)
    (M := m) (R := R) (r := 1) (X := X) (C := C) (Mf := mf)
    (by norm_num) hrho heta (by norm_num) hX hC hmf hm hshift hslope).1
  obtain ⟨hP, hpairs⟩ := fw_wheel_binned_pairs S X L R hX hL hR hbefore
    (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)
  let short := P.filter fun x => ((x.2 - x.1 : ℕ) : ℝ) < D
  let long := P.filter fun x => D ≤ ((x.2 - x.1 : ℕ) : ℝ)
  have hshort := fw_affine_short_pair_count S P W D rho C hne hWodd
    (fun p hp => ⟨(hS p hp).2.1, (hS p hp).2.2⟩)
    (fun x hx => ⟨(hP x hx).1, (hP x hx).2.1, (hP x hx).2.2.1, (hP x hx).2.2.2.1⟩)
    hD hrho hdisc
  change (short.card : ℝ) < N * (rho * D / 2 + C) at hshort
  have hpart : short.card + long.card = P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := P)
      (fun x => ((x.2 - x.1 : ℕ) : ℝ) < D)
    simpa [short, long, not_lt] using h
  have hpartR : (short.card : ℝ) + long.card = P.card := by exact_mod_cast hpart
  have hpairs' : c0 * N^2 * (R : ℝ) / ((1 : ℝ) * X) - N / 2 ≤ (P.card : ℝ) := by
    dsimp [c0, N, P]
    simpa using hpairs
  have hquota' : 2 * (((z * Q : ℕ) : ℝ)) * (1 : ℝ) * X ≤
      (c0 - eta) * mf^2 * 2 := by
    dsimp [c0]
    nlinarith [hquota]
  have hlong0 := affine_pair_population_real (N := N) (M := m) (Mf := mf)
    (R := (R : ℝ)) (X := X) (r := 1) (eta := eta) (c₀ := c0) (rho := rho)
    (g := 2) (C := C) (D := D) (P := (P.card : ℝ)) (short := (short.card : ℝ))
    (Z := ((z * Q : ℕ) : ℝ)) hRreal hX (by norm_num) (by norm_num) hrho
    heta.le heps' hmf.le hm hNge (by rfl) hpairs' hshort hquota'
  have hlong : ((z * Q : ℕ) : ℝ) * R < (long.card : ℝ) := by
    nlinarith [hlong0, hpartR]
  have hreal : ((((R / 2) * (2 * (z * Q)) : ℕ) : ℝ)) ≤ ((z * Q : ℕ) : ℝ) * R := by
    have hdiv : (R / 2) * 2 = R := Nat.div_mul_cancel heven
    have hn : (R / 2) * (2 * (z * Q)) = (z * Q) * R := by
      calc
        _ = ((R / 2) * 2) * (z * Q) := by ac_rfl
        _ = (z * Q) * R := by rw [hdiv]; ac_rfl
    exact_mod_cast (le_of_eq hn)
  have hcount : (R / 2) * (2 * (z * Q)) ≤ long.card := by
    exact_mod_cast (hreal.trans (le_of_lt hlong))
  have hvalid : ∀ x ∈ long, x.1 < x.2 ∧ 2 ∣ x.2 - x.1 ∧
      x.2 - x.1 ≤ R ∧ D ≤ ((x.2 - x.1 : ℕ) : ℝ) := by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).1
    have hs := hP x hp
    refine ⟨hs.2.2.1, ?_, hs.2.2.2.2, (Finset.mem_filter.mp hx).2⟩
    omega
  obtain ⟨gap, chosen, hgap, hdiv, hmax, hlow, hcard, hmem, hmatching⟩ :=
    fw_weak_common_gap_matching_from_pairs long 2 R (z * Q) D (by decide) (by omega) hzQ hvalid hcount
  refine ⟨gap, chosen, hgap, hdiv, hlow, hmax, hcard, ?_, ?_, hmatching⟩
  · intro p hp
    exact (Finset.mem_filter.mp (hmem p hp)).1
  · intro p hp
    have hp' := (Finset.mem_filter.mp (hmem p hp)).1
    exact ⟨(hP (p, p + gap) hp').1, (hP (p, p + gap) hp').2.1⟩


end Sude
