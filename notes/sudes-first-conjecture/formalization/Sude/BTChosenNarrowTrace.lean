import Sude.BTStageDepletion
import Sude.FWWheelFirstTraceStep

/-! Append one Brun--Titchmarsh stage while charging only its retained pairs.
The prime-distribution input and the exact finite pair gate are explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Select `6Q` actual disjoint candidates at one even gap, narrow them to
`Q` pairs, and append precisely those retained pairs to the supplied trace.
Discarded candidates are not charged to the stock. -/
theorem BTGrowingTrace.append_bt_six_narrow_matching
    {Q : ℕ} {initial unused : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (mv : MVBrunTitchmarsh) (trace : BTGrowingTrace 2 Q initial radius unused last stages)
    (classes : Finset ℕ) (lo W width ell midpointWidth : ℝ) (R : ℕ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + W)
    (hclasses : ∀ p ∈ unused, p % 2 ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime 2 a)
    (hR : 0 < R) (hRlast : R ≤ last) (hwidth : (2 : ℝ) < width)
    (hell : 0 < ell) (hexp : Real.exp ell ≤ width / 2)
    (hgate : (((⌊(R : ℝ)⌋₊ / 2) * (2 * (6 * Q)) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient 2 : ℝ) * ell)) ≤
        ((unused.card : ℝ) ^ 2 / ((⌊W / (R : ℝ)⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2)
    (hmidWidth : 0 < midpointWidth)
    (hcap : ∀ p ∈ unused, (p : ℝ) ≤ 6 * midpointWidth) :
    ∃ (gap : ℕ) (candidates chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ gap ≤ R ∧ width ≤ gap ∧
      candidates.card = 6 * Q ∧ PairwiseDisjointPairs candidates gap ∧
      pairFootprint candidates gap ⊆ unused ∧ chosen ⊆ candidates ∧ chosen.card = Q ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ unused ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (unused \ pairFootprint chosen gap).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| < midpointWidth) ∧
      BTGrowingTrace 2 Q initial radius (unused \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, width⟩]) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  obtain ⟨gap, candidates, hgap, heven, hgapR, hmin, hcount, hmatch, hfoot, _, _⟩ :=
    mv_interval_stage_select_and_deplete mv unused classes lo W R width ell 2 (6 * Q)
      hne hprimes hinterval hclasses hreduced (by decide) hRreal hwidth hell hexp hgate
  have hgapR' : gap ≤ R := by simpa using hgapR
  have hspan : ∀ p ∈ candidates, (0 : ℝ) ≤ p ∧ (p : ℝ) < 0 + 6 * midpointWidth := by
    intro p hp
    have hpnext : p + gap ∈ unused :=
      hfoot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    have hbound := hcap (p + gap) hpnext
    have hgapreal : (0 : ℝ) < gap := by exact_mod_cast hgap
    push_cast at hbound
    constructor <;> linarith
  obtain ⟨chosen, hsub, hchosen, hmatching, hsubset, hfootcard, hremaining, hnarrow, htrace⟩ :=
    trace.append_narrow_matching (z := 6) candidates gap width 0 midpointWidth
      hgap heven (hgapR'.trans hRlast) hmin (by decide) hmidWidth hspan (by omega) hmatch hfoot
  exact ⟨gap, candidates, chosen, hgap, heven, hgapR', hmin, hcount, hmatch, hfoot,
    hsub, hchosen, hmatching, hsubset, hfootcard, hremaining, hnarrow, htrace⟩

end
end Sude
