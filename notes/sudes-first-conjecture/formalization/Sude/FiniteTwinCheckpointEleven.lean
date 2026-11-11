import Sude.FiniteTwinCheckpointTen
import Sude.GeneratedTwinScan.S008All

/-! Add the checked adjacent S008 interval to the partial FT population. -/
namespace Sude
noncomputable section

/-- Nine adjacent low segments contain exactly 102,214 lower endpoints. -/
theorem finiteTwinFirstNineSegments : (twinPrimeSegment 45 18874413).card = 102214 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 16777261)
    (by decide : 16777261 ≤ 18874413)
    finiteTwinFirstEightSegments GeneratedTwinScan.S008All.total

/-- Nine low segments, two checked middle segments and the separate
high-end block give 115,872 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_115872 : 115872 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 18874413
  let mid := twinPrimeSegment 538968109 543162413
  let hi := twinPrimeSegment 1073709055 1073741823
  have hdis_lh : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [lo, hi, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp hq
    omega
  have hdis_lm : Disjoint lo mid := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [lo, mid, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp hq
    omega
  have hdis_hm : Disjoint hi mid := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [hi, mid, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp hq
    omega
  have hdis : Disjoint (lo ∪ hi) mid := Finset.disjoint_union_left.mpr ⟨hdis_lm, hdis_hm⟩
  have hsub : (lo ∪ hi) ∪ mid ⊆ finiteTwinSeeds := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · simp only [lo, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
        exact (mem_finiteTwinSeeds p).mpr ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
      · simp only [hi, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
        exact (mem_finiteTwinSeeds p).mpr ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
    · simp only [mid, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
      exact (mem_finiteTwinSeeds p).mpr ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hdis_lh] at h
  have hlo : lo.card = 102214 := finiteTwinFirstNineSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
