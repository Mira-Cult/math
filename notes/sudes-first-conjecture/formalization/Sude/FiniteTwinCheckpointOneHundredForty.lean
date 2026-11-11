import Sude.FiniteTwinCheckpointOneHundredThirtyTwo
import Sude.GeneratedTwinScan.S130All
import Sude.GeneratedTwinScan.S131All
import Sude.GeneratedTwinScan.S132All
import Sude.GeneratedTwinScan.S133All
import Sude.GeneratedTwinScan.S134All
import Sude.GeneratedTwinScan.S135All
import Sude.GeneratedTwinScan.S136All
import Sude.GeneratedTwinScan.S137All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred thirty-eight adjacent low segments contain exactly 1,129,704 lower endpoints. -/
theorem finiteTwinFirstOneHundredThirtyEightSegments : (twinPrimeSegment 45 289407021).card = 1129704 := by
  have h130 : (twinPrimeSegment 45 274726957).card = 1078256 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 272629805)
      (by decide : 272629805 ≤ 274726957) finiteTwinFirstOneHundredThirtySegments GeneratedTwinScan.S130All.total
  have h131 : (twinPrimeSegment 45 276824109).card = 1085555 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 274726957)
      (by decide : 274726957 ≤ 276824109) h130 GeneratedTwinScan.S131All.total
  have h132 : (twinPrimeSegment 45 278921261).card = 1092879 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 276824109)
      (by decide : 276824109 ≤ 278921261) h131 GeneratedTwinScan.S132All.total
  have h133 : (twinPrimeSegment 45 281018413).card = 1100310 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 278921261)
      (by decide : 278921261 ≤ 281018413) h132 GeneratedTwinScan.S133All.total
  have h134 : (twinPrimeSegment 45 283115565).card = 1107643 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 281018413)
      (by decide : 281018413 ≤ 283115565) h133 GeneratedTwinScan.S134All.total
  have h135 : (twinPrimeSegment 45 285212717).card = 1114955 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 283115565)
      (by decide : 283115565 ≤ 285212717) h134 GeneratedTwinScan.S135All.total
  have h136 : (twinPrimeSegment 45 287309869).card = 1122321 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 285212717)
      (by decide : 285212717 ≤ 287309869) h135 GeneratedTwinScan.S136All.total
  have h137 : (twinPrimeSegment 45 289407021).card = 1129704 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 287309869)
      (by decide : 287309869 ≤ 289407021) h136 GeneratedTwinScan.S137All.total
  exact h137

/-- One hundred thirty-eight low segments, two checked middle segments and the separate
high-end block give 1,143,362 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1143362 : 1143362 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 289407021
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
  have hlo : lo.card = 1129704 := finiteTwinFirstOneHundredThirtyEightSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
