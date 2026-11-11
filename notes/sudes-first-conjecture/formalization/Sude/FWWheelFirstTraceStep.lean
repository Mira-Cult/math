import Sude.FWWheelTraceNextCandidates
import Sude.BTGrowingCompose
import Sude.PhysicalNarrowing

/-! Narrow and append one supplied first-wheel candidate matching. The
source's candidate and numerical premises remain explicit; this module does
not construct the preceding trace or later physical growth. -/
namespace Sude
noncomputable section

/-- Append one narrowed selected matching to an existing growing trace.
Only actual retained endpoints are removed. -/
theorem BTGrowingTrace.append_narrow_matching
    {g Q z : ℕ} {initial unused : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius unused last stages)
    (candidates : Finset ℕ) (gap : ℕ) (minimum lo width : ℝ)
    (hgap : 0 < gap) (hdiv : g ∣ gap) (hbound : gap ≤ last)
    (hminimum : minimum ≤ gap)
    (hz : 0 < z) (hwidth : 0 < width)
    (hspan : ∀ p ∈ candidates, lo ≤ p ∧ (p : ℝ) < lo + z * width)
    (hcount : z * Q ≤ candidates.card)
    (hmatch : PairwiseDisjointPairs candidates gap)
    (hfoot : pairFootprint candidates gap ⊆ unused) :
    ∃ chosen : Finset ℕ,
      chosen ⊆ candidates ∧ chosen.card = Q ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ unused ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (unused \ pairFootprint chosen gap).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| < width) ∧
      BTGrowingTrace g Q initial radius (unused \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, minimum⟩]) := by
  have havail : ∀ p ∈ candidates, p ∈ unused ∧ p + gap ∈ unused := by
    intro p hp
    exact ⟨hfoot (Finset.mem_union_left _ hp),
      hfoot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))⟩
  obtain ⟨chosen, hsub, hc, hm, hs, hf, hd, hn⟩ :=
    narrow_matching_and_deplete unused candidates lo width z Q gap hz hwidth hgap
      hspan hcount havail hmatch
  let stage : BTSelectedStage := ⟨gap, chosen, minimum⟩
  have hsingle : BTGrowingTrace g Q unused last (unused \ pairFootprint chosen gap)
      (last + gap) [stage] := by
    exact BTGrowingTrace.cons unused last stage _ _ [] hgap hdiv hbound hminimum hc hm hs
      (BTGrowingTrace.nil _ _)
  refine ⟨chosen, hsub, hc, hm, hs, hf, hd, hn, ?_⟩
  exact trace.append hsingle


/-- A supplied first FW wheel matching produces one actual narrowed stage.
The selected lower endpoints remain a subset of the source candidates; the
certified radius uses the exact first-wheel WW5 cutoff, while the actual
radius advances by the selected gap. -/
theorem fw_first_wheel_append_supplied_candidates {n : ℕ}
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius final last stages)
    (R T gap : ℕ) (candidates : Finset ℕ)
    (hRlast : R ≤ last)
    (hgap : 0 < gap) (hdiv : 2 ∣ gap) (hgapR : gap ≤ R)
    (hminimum : 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (R / 2) ≤ gap)
    (hcount : 6 * (6 * (n + 8)) ≤ candidates.card)
    (hmatch : PairwiseDisjointPairs candidates gap)
    (hfoot : pairFootprint candidates gap ⊆ final)
    (hcap : ∀ p ∈ final, (p : ℝ) ≤ poolMaximum n) :
    let cutoff := 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (R / 2)
    ∃ chosen : Finset ℕ,
      chosen ⊆ candidates ∧ chosen.card = 6 * (n + 8) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ final ∧
      (pairFootprint chosen gap).card = 2 * (6 * (n + 8)) ∧
      (final \ pairFootprint chosen gap).card + 2 * (6 * (n + 8)) = final.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
          (poolMaximum n : ℝ) / 6) ∧
      R + cutoff ≤ last + gap ∧
      BTGrowingTrace 2 (6 * (n + 8)) initial radius
        (final \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, (cutoff : ℝ)⟩]) := by
  dsimp only
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hspan : ∀ p ∈ candidates, (0 : ℝ) ≤ p ∧
      (p : ℝ) < 0 + (6 : ℕ) * ((poolMaximum n : ℝ) / 6) := by
    intro p hp
    have hpnext : p + gap ∈ final :=
      hfoot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    have hbound := hcap (p + gap) hpnext
    have hgap' : (0 : ℝ) < (gap : ℝ) := by exact_mod_cast hgap
    push_cast at hbound
    constructor <;> linarith
  have hminReal : ((2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (R / 2) : ℕ) : ℝ) ≤ gap := by
    exact_mod_cast hminimum
  obtain ⟨chosen, hcand, hc, hm, hs, hf, hd, hn, htrace⟩ :=
    trace.append_narrow_matching (z := 6) candidates gap _ 0 ((poolMaximum n : ℝ) / 6)
      hgap hdiv (hgapR.trans hRlast) hminReal (by norm_num) (by positivity)
      hspan hcount hmatch hfoot
  exact ⟨chosen, hcand, hc, hm, hs, hf, hd, hn, by omega, htrace⟩


/-- Under the source first-wheel stock and floor premises, select and append
one narrowed stage to the supplied trace. No later recipe or placement is asserted. -/
theorem fw_wheel_trace_first_window_append {n : ℕ} (hn : 13 ≤ n * n)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (R : ℕ) (L m mf eta qbar : ℝ)
    (hR : 0 < R) (heven : 2 ∣ R) (hRlast : R ≤ last) (hL : 0 < L)
    (hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / L)
    (hmf : 0 ≤ mf) (hm : mf ≤ m) (heta : 0 ≤ eta)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hmBound : m ≤ (((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) / (poolMaximum n : ℝ))
    (hA : 0 ≤ eta * m * R - 1 / 2)
    (hq : ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * (poolMaximum n : ℝ))
    (hquota : 2 * (1 / (2 * (1 + 1 / L)) - eta) * mf ^ 2 ≥ 2 * (6 : ℝ) * qbar) :
    let Q := 6 * (n + 8)
    let P := sameClassPairs final (progressionBinKey 0 R 2)
    let T := ⌊eta * m * R - 1 / 2⌋₊
    let cutoff := 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (R / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ cutoff ≤ gap ∧ gap ≤ R ∧
      chosen.card = Q ∧ (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (final \ pairFootprint chosen gap).card + 2 * Q = final.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
          (poolMaximum n : ℝ) / 6) ∧
      R + cutoff ≤ last + gap ∧
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        radius (final \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, (cutoff : ℝ)⟩]) := by
  dsimp only
  let T : ℕ := ⌊eta * m * R - 1 / 2⌋₊
  obtain ⟨gap, selected, hgap, hdiv, hmin, hmax, hlast, hnum, hpairs, havail, havoids, hmatch⟩ :=
    fw_wheel_trace_first_window_candidates hn batches hvalid candidates hcard kept hsub hkept hinj
      blocks hblocks radius last final stages trace R L m mf eta qbar hR heven hRlast hL
      hnotdone hmf hm heta heps hmBound hA hq hquota
  have hcap : ∀ p ∈ final, (p : ℝ) ≤ poolMaximum n := by
    intro p hp
    exact (fw_wheel_witness_trace_screened_units batches candidates hcard kept hsub blocks
      radius last final stages trace p hp).2.2.2.2
  obtain ⟨chosen, hchosen, hcard', hmatch', hsub', hsize, hdeplete, hmid, hradius, htrace⟩ :=
    fw_first_wheel_append_supplied_candidates trace R T gap selected hRlast hgap hdiv hmax
      hmin hnum hmatch havail hcap
  have hsubset : pairFootprint chosen gap ⊆ pairFootprint selected gap := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hchosen hx)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hchosen hp, rfl⟩)
  have havoid' := havoids.mono_left hsubset
  exact ⟨gap, chosen, hgap, hdiv, hmin, hmax, hcard',
    (fun p hp => hpairs p (hchosen hp)), hmatch', hsub', havoid', hsize, hdeplete, hmid,
    hradius, htrace⟩


end
end Sude
