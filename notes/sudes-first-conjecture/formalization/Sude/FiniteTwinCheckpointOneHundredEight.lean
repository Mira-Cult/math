import Sude.FiniteTwinCheckpointOneHundred
import Sude.GeneratedTwinScan.S098All
import Sude.GeneratedTwinScan.S099All
import Sude.GeneratedTwinScan.S100All
import Sude.GeneratedTwinScan.S101All
import Sude.GeneratedTwinScan.S102All
import Sude.GeneratedTwinScan.S103All
import Sude.GeneratedTwinScan.S104All
import Sude.GeneratedTwinScan.S105All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred six adjacent low segments contain exactly 893,212 lower endpoints. -/
theorem finiteTwinFirstOneHundredSixSegments : (twinPrimeSegment 45 222298157).card = 893212 := by
  have h98 : (twinPrimeSegment 45 207618093).card = 840680 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 205520941)
      (by decide : 205520941 ≤ 207618093) finiteTwinFirstNinetyEightSegments GeneratedTwinScan.S098All.total
  have h99 : (twinPrimeSegment 45 209715245).card = 848299 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 207618093)
      (by decide : 207618093 ≤ 209715245) h98 GeneratedTwinScan.S099All.total
  have h100 : (twinPrimeSegment 45 211812397).card = 855847 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 209715245)
      (by decide : 209715245 ≤ 211812397) h99 GeneratedTwinScan.S100All.total
  have h101 : (twinPrimeSegment 45 213909549).card = 863367 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 211812397)
      (by decide : 211812397 ≤ 213909549) h100 GeneratedTwinScan.S101All.total
  have h102 : (twinPrimeSegment 45 216006701).card = 870909 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 213909549)
      (by decide : 213909549 ≤ 216006701) h101 GeneratedTwinScan.S102All.total
  have h103 : (twinPrimeSegment 45 218103853).card = 878270 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 216006701)
      (by decide : 216006701 ≤ 218103853) h102 GeneratedTwinScan.S103All.total
  have h104 : (twinPrimeSegment 45 220201005).card = 885682 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 218103853)
      (by decide : 218103853 ≤ 220201005) h103 GeneratedTwinScan.S104All.total
  have h105 : (twinPrimeSegment 45 222298157).card = 893212 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 220201005)
      (by decide : 220201005 ≤ 222298157) h104 GeneratedTwinScan.S105All.total
  exact h105

/-- One hundred six low segments, two checked middle segments and the separate
high-end block give 906,870 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_906870 : 906870 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 222298157
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
  have hlo : lo.card = 893212 := finiteTwinFirstOneHundredSixSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
