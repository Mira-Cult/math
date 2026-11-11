import Sude.FiniteTwinCheckpointTwoHundredTwentyEight
import Sude.GeneratedTwinScan.S226All
import Sude.GeneratedTwinScan.S227All
import Sude.GeneratedTwinScan.S228All
import Sude.GeneratedTwinScan.S229All
import Sude.GeneratedTwinScan.S230All
import Sude.GeneratedTwinScan.S231All
import Sude.GeneratedTwinScan.S232All
import Sude.GeneratedTwinScan.S233All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Two hundred thirty-four adjacent low segments contain exactly 1,809,682 lower endpoints. -/
theorem finiteTwinFirstTwoHundredThirtyFourSegments : (twinPrimeSegment 45 490733613).card = 1809682 := by
  have h226 : (twinPrimeSegment 45 476053549).card = 1761407 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 473956397)
      (by decide : 473956397 ≤ 476053549) finiteTwinFirstTwoHundredTwentySixSegments GeneratedTwinScan.S226All.total
  have h227 : (twinPrimeSegment 45 478150701).card = 1768390 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 476053549)
      (by decide : 476053549 ≤ 478150701) h226 GeneratedTwinScan.S227All.total
  have h228 : (twinPrimeSegment 45 480247853).card = 1775350 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 478150701)
      (by decide : 478150701 ≤ 480247853) h227 GeneratedTwinScan.S228All.total
  have h229 : (twinPrimeSegment 45 482345005).card = 1782159 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 480247853)
      (by decide : 480247853 ≤ 482345005) h228 GeneratedTwinScan.S229All.total
  have h230 : (twinPrimeSegment 45 484442157).card = 1789069 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 482345005)
      (by decide : 482345005 ≤ 484442157) h229 GeneratedTwinScan.S230All.total
  have h231 : (twinPrimeSegment 45 486539309).card = 1795920 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 484442157)
      (by decide : 484442157 ≤ 486539309) h230 GeneratedTwinScan.S231All.total
  have h232 : (twinPrimeSegment 45 488636461).card = 1802796 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 486539309)
      (by decide : 486539309 ≤ 488636461) h231 GeneratedTwinScan.S232All.total
  have h233 : (twinPrimeSegment 45 490733613).card = 1809682 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 488636461)
      (by decide : 488636461 ≤ 490733613) h232 GeneratedTwinScan.S233All.total
  exact h233

/-- Two hundred thirty-four low segments, two checked middle segments and the separate
high-end block give 1,823,340 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1823340 : 1823340 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 490733613
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
  have hlo : lo.card = 1809682 := finiteTwinFirstTwoHundredThirtyFourSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
