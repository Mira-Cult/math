import Sude.FiniteTwinCheckpointOneHundredSixtyFour
import Sude.GeneratedTwinScan.S162All
import Sude.GeneratedTwinScan.S163All
import Sude.GeneratedTwinScan.S164All
import Sude.GeneratedTwinScan.S165All
import Sude.GeneratedTwinScan.S166All
import Sude.GeneratedTwinScan.S167All
import Sude.GeneratedTwinScan.S168All
import Sude.GeneratedTwinScan.S169All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred seventy adjacent low segments contain exactly 1,360,628 lower endpoints. -/
theorem finiteTwinFirstOneHundredSeventySegments : (twinPrimeSegment 45 356515885).card = 1360628 := by
  have h162 : (twinPrimeSegment 45 341835821).card = 1310650 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 339738669)
      (by decide : 339738669 ≤ 341835821) finiteTwinFirstOneHundredSixtyTwoSegments GeneratedTwinScan.S162All.total
  have h163 : (twinPrimeSegment 45 343932973).card = 1317854 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 341835821)
      (by decide : 341835821 ≤ 343932973) h162 GeneratedTwinScan.S163All.total
  have h164 : (twinPrimeSegment 45 346030125).card = 1325080 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 343932973)
      (by decide : 343932973 ≤ 346030125) h163 GeneratedTwinScan.S164All.total
  have h165 : (twinPrimeSegment 45 348127277).card = 1332208 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 346030125)
      (by decide : 346030125 ≤ 348127277) h164 GeneratedTwinScan.S165All.total
  have h166 : (twinPrimeSegment 45 350224429).card = 1339330 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 348127277)
      (by decide : 348127277 ≤ 350224429) h165 GeneratedTwinScan.S166All.total
  have h167 : (twinPrimeSegment 45 352321581).card = 1346370 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 350224429)
      (by decide : 350224429 ≤ 352321581) h166 GeneratedTwinScan.S167All.total
  have h168 : (twinPrimeSegment 45 354418733).card = 1353430 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 352321581)
      (by decide : 352321581 ≤ 354418733) h167 GeneratedTwinScan.S168All.total
  have h169 : (twinPrimeSegment 45 356515885).card = 1360628 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 354418733)
      (by decide : 354418733 ≤ 356515885) h168 GeneratedTwinScan.S169All.total
  exact h169

/-- One hundred seventy low segments, two checked middle segments and the separate
high-end block give 1,374,286 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1374286 : 1374286 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 356515885
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
  have hlo : lo.card = 1360628 := finiteTwinFirstOneHundredSeventySegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
