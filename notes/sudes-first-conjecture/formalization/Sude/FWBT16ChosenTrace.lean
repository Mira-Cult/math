import Sude.BTChosenNarrowTrace
import Sude.FWBT16FirstBandBudget

/-! The conditional first-band BT16 one-stage gate, for an actual supplied
trace and stock. The Montgomery--Vaughan input remains explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- At a paid radius and under the source stock and pair budgets, select a
`6Q` common-gap matching, narrow it to `Q`, and append only those pairs. -/
theorem BTGrowingTrace.append_fw_bt16_first_band
    {Q : ℕ} {initial unused : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (mv : MVBrunTitchmarsh) (trace : BTGrowingTrace 2 Q initial radius unused last stages)
    (X : ℝ) (R : ℕ) (classes : Finset ℕ)
    (hsteps : stages.length ≤ 238) (hX : 0 < X)
    (hQ : (Q : ℝ) ≤ (1 / 69780 : ℝ) * X)
    (hR : 171331843 ≤ R) (hRlast : R ≤ last) (hRcap : (R : ℝ) ≤ X / 23)
    (hstock : fwFirstBandMu stages.length * X ≤ unused.card)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hclasses : ∀ p ∈ unused, p % 2 ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime 2 a)
    (hclasscount : (classes.card : ℝ) ≤ 1)
    (hcap : ∀ p ∈ unused, (p : ℝ) ≤ X) :
    let D := 8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu stages.length * R - 1 / 2)
    ∃ (gap : ℕ) (candidates chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ gap ≤ R ∧ D ≤ gap ∧
      candidates.card = 6 * Q ∧ PairwiseDisjointPairs candidates gap ∧
      pairFootprint candidates gap ⊆ unused ∧ chosen ⊆ candidates ∧ chosen.card = Q ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ unused ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (unused \ pairFootprint chosen gap).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| < X / 6) ∧
      BTGrowingTrace 2 Q initial radius (unused \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, D⟩]) := by
  dsimp only
  let D : ℝ := 8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu stages.length * R - 1 / 2)
  let M : ℝ := fwFirstBandMu stages.length * X
  obtain ⟨hDpos, hDle, hDexp, hbudget⟩ :=
    fw_bt16_first_band_width_and_budget (j := stages.length) (Q := Q) (R := R) hsteps hX hQ hR
  have hM : 0 ≤ M := by
    dsimp [M]
    exact (mul_pos (fw_first_band_full_stock_quota_slack hsteps).2.1 hX).le
  have hRpos : 0 < R := by omega
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hclassespos : 0 < classes.card := by
    obtain ⟨p, hp⟩ := hne
    exact Finset.card_pos.mpr ⟨p % 2, hclasses p hp⟩
  have hwidthEq : D = (16 * (Nat.totient 2 : ℝ) / (2 * (2 : ℕ))) * 2 *
      ((3981035 / 10000000 : ℝ) * M * R / (1 * X) - 1 / 2) := by
    dsimp [D, M]
    norm_num
    field_simp
  have hgate := bt_source_implies_exact_bin_gate unused classes 1 X 1 R 23
    (3981035 / 10000000) M 16 D 2 (6 * Q) hM hstock (by norm_num) hX
    (by norm_num) hRreal (by norm_num) (by decide) (by norm_num) hclassespos hclasscount
    (by norm_num) (by norm_num) hRcap hwidthEq (by simpa [M] using hbudget)
  have hgate' : (((⌊(R : ℝ)⌋₊ / 2) * (2 * (6 * Q)) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * D / ((Nat.totient 2 : ℝ) * 16)) ≤
        ((unused.card : ℝ) ^ 2 / ((⌊X / (R : ℝ)⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2 := by
    simpa using hgate
  have hinterval : ∀ p ∈ unused, (0 : ℝ) ≤ p ∧ (p : ℝ) ≤ 0 + X := by
    intro p hp
    exact ⟨by positivity, by simpa using hcap p hp⟩
  have hmid : 0 < X / 6 := by positivity
  have hcap' : ∀ p ∈ unused, (p : ℝ) ≤ 6 * (X / 6) := by
    intro p hp
    linarith [hcap p hp]
  exact trace.append_bt_six_narrow_matching mv classes 0 X D 16 (X / 6) R hne hprimes
    hinterval hclasses hreduced hRpos hRlast (by simpa [D] using hDpos) (by norm_num)
    (by simpa [D] using hDexp) hgate' hmid hcap'

end
end Sude
