import Sude.FiniteTwinCheckpointOneHundredSixteen
import Sude.GeneratedTwinScan.S114All
import Sude.GeneratedTwinScan.S115All
import Sude.GeneratedTwinScan.S116All
import Sude.GeneratedTwinScan.S117All
import Sude.GeneratedTwinScan.S118All
import Sude.GeneratedTwinScan.S119All
import Sude.GeneratedTwinScan.S120All
import Sude.GeneratedTwinScan.S121All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred twenty-two adjacent low segments contain exactly 1,012,210 lower endpoints. -/
theorem finiteTwinFirstOneHundredTwentyTwoSegments : (twinPrimeSegment 45 255852589).card = 1012210 := by
  have h114 : (twinPrimeSegment 45 241172525).card = 960361 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 239075373)
      (by decide : 239075373 ≤ 241172525) finiteTwinFirstOneHundredFourteenSegments GeneratedTwinScan.S114All.total
  have h115 : (twinPrimeSegment 45 243269677).card = 967786 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 241172525)
      (by decide : 241172525 ≤ 243269677) h114 GeneratedTwinScan.S115All.total
  have h116 : (twinPrimeSegment 45 245366829).card = 975266 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 243269677)
      (by decide : 243269677 ≤ 245366829) h115 GeneratedTwinScan.S116All.total
  have h117 : (twinPrimeSegment 45 247463981).card = 982561 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 245366829)
      (by decide : 245366829 ≤ 247463981) h116 GeneratedTwinScan.S117All.total
  have h118 : (twinPrimeSegment 45 249561133).card = 989926 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 247463981)
      (by decide : 247463981 ≤ 249561133) h117 GeneratedTwinScan.S118All.total
  have h119 : (twinPrimeSegment 45 251658285).card = 997299 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 249561133)
      (by decide : 249561133 ≤ 251658285) h118 GeneratedTwinScan.S119All.total
  have h120 : (twinPrimeSegment 45 253755437).card = 1004712 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 251658285)
      (by decide : 251658285 ≤ 253755437) h119 GeneratedTwinScan.S120All.total
  have h121 : (twinPrimeSegment 45 255852589).card = 1012210 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 253755437)
      (by decide : 253755437 ≤ 255852589) h120 GeneratedTwinScan.S121All.total
  exact h121

/-- One hundred twenty-two low segments, two checked middle segments and the separate
high-end block give 1,025,868 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1025868 : 1025868 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 255852589
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
  have hlo : lo.card = 1012210 := finiteTwinFirstOneHundredTwentyTwoSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
