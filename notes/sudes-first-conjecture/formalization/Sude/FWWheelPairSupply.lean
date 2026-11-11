import Sude.FWWheelStockGate
import Sude.BTIntervalBins

/-! Finite source WW3 pair supply from actual spatial bins. No numerical
stock gate or growth trace is asserted. See WW3 in
`problems/prime-line-sums/manuscripts/cutoff2_exact_wheel_window.md`. -/
namespace Sude
noncomputable section

/-- The actual number of half-open radius-R bins is bounded by the source's
continuous bin envelope before the stopping threshold X/L. -/
theorem fw_wheel_bin_count_bound (X L : ℝ) (R : ℕ)
    (hX : 0 < X) (hL : 0 < L) (hR : 0 < R) (hbefore : (R : ℝ) ≤ X / L) :
    ((⌊X / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ (1 + 1 / L) * X / R := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hfloor := Nat.floor_le (show 0 ≤ X / (R : ℝ) by positivity)
  have hRL : (R : ℝ) * L ≤ X := (le_div_iff₀ hL).mp hbefore
  have hratio : 1 ≤ (X / (R : ℝ)) / L := by
    apply (le_div_iff₀ hL).2
    apply (le_div_iff₀ hR').2
    nlinarith
  push_cast
  calc
    _ ≤ X / (R : ℝ) + 1 := by linarith
    _ ≤ X / (R : ℝ) + (X / (R : ℝ)) / L := by linarith
    _ = _ := by ring

/-- Same spatial-bin pairs have the source's explicit Cauchy lower bound.
The finite set and every numerical condition are supplied. -/
theorem fw_wheel_binned_pairs (S : Finset ℕ) (X L : ℝ) (R : ℕ)
    (hX : 0 < X) (hL : 0 < L) (hR : 0 < R) (hbefore : (R : ℝ) ≤ X / L)
    (hS : ∀ p ∈ S, (p : ℝ) ≤ X ∧ p % 2 = 1) :
    let key := progressionBinKey 0 R 2
    let P := sameClassPairs S key
    (∀ x ∈ P, x.1 ∈ S ∧ x.2 ∈ S ∧ x.1 < x.2 ∧
      x.2 % 2 = x.1 % 2 ∧ x.2 - x.1 ≤ R) ∧
    (1 / (2 * (1 + 1 / L)) : ℝ) * (S.card : ℝ)^2 * R / X -
      (S.card : ℝ) / 2 ≤ P.card := by
  classical
  dsimp only
  let key := progressionBinKey 0 R 2
  let B : ℕ := ⌊X / (R : ℝ)⌋₊ + 1
  let D : ℝ := (1 + 1 / L) * X / R
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hinterval : ∀ p ∈ S, (0 : ℝ) ≤ p ∧ (p : ℝ) ≤ 0 + X := by
    intro p hp
    exact ⟨by positivity, by simpa using (hS p hp).1⟩
  have hclasses : ∀ p ∈ S, p % 2 ∈ ({1} : Finset ℕ) := by
    intro p hp
    simpa using (hS p hp).2
  have hkey := progression_bin_key_card S {1} 0 X R 2 hR' hinterval hclasses
  have hB : (S.image key).card ≤ B := by simpa [key, B] using hkey
  have hBpos : 0 < B := by dsimp [B]; omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hbound : (B : ℝ) ≤ D := by
    simpa [B, D] using fw_wheel_bin_count_bound X L R hX hL hR hbefore
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (S.card : ℝ)) hBR hbound
  have hpair := sameClassPairs_lower_bound S key B hB hBpos
  have hidentity : ((S.card : ℝ)^2 / D) / 2 =
      (1 / (2 * (1 + 1 / L)) : ℝ) * (S.card : ℝ)^2 * R / X := by
    dsimp [D]
    field_simp
  constructor
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hmem := Finset.mem_product.mp hx'.1
    have hlt := hx'.2.1
    have hkeys := hx'.2.2
    have hgeom := progression_bin_key_pair hR' (hinterval x.1 hmem.1).1 hlt hkeys
    have hparity := congrArg Prod.snd hkeys
    exact ⟨hmem.1, hmem.2, hlt, hparity.symm, by simpa using hgeom.2.1⟩
  · rw [← hidentity]
    linarith

/-- At a supplied pre-crossing radius, the actual spatial-bin pair set and
explicit WW4 stock inequalities yield the WW5 equal-gap matching. Nothing here
asserts those stock inequalities or an iterable growth trace. -/
theorem fw_wheel_ww5_common_gap_from_bins
    (S : Finset ℕ) (W R z Q : ℕ) (X L m mf eta qbar : ℝ)
    (hW : 0 < W) (hWodd : W % 2 = 1) (hR : 0 < R) (heven : 2 ∣ R)
    (hzQ : 0 < z * Q) (hX : 0 < X) (hL : 0 < L) (hbefore : (R : ℝ) ≤ X / L)
    (hS : ∀ p ∈ S, (p : ℝ) ≤ X ∧ p % 2 = 1 ∧ Nat.Coprime p W)
    (hmf : 0 ≤ mf) (hm : mf ≤ m) (heta : 0 ≤ eta)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hstock : m * X ≤ (S.card : ℝ)) (hA : 0 ≤ eta * m * R - 1 / 2)
    (hq : (Q : ℝ) ≤ qbar * X)
    (hquota : 2 * (1 / (2 * (1 + 1 / L)) - eta) * mf ^ 2 ≥
      2 * (z : ℝ) * qbar) :
    let P := sameClassPairs S (progressionBinKey 0 R 2)
    let T := ⌊eta * m * R - 1 / 2⌋₊
    let k := fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)
    let h := 2 * min k (R / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ h ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  dsimp only
  let P := sameClassPairs S (progressionBinKey 0 R 2)
  have hS' : ∀ p ∈ S, (p : ℝ) ≤ X ∧ p % 2 = 1 := by
    intro p hp
    exact ⟨(hS p hp).1, (hS p hp).2.1⟩
  obtain ⟨hP, hpairs⟩ := fw_wheel_binned_pairs S X L R hX hL hR hbefore hS'
  exact fw_wheel_ww5_common_gap_from_stock S P W R z Q X m mf eta
    (1 / (2 * (1 + 1 / L))) qbar hW hWodd hR heven hzQ
    (fun p hp => ⟨(hS p hp).2.1, (hS p hp).2.2⟩) hP hX hmf hm heta heps
    hstock hA hq hquota hpairs


end
end Sude
