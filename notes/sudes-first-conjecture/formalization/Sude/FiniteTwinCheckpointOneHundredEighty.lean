import Sude.FiniteTwinCheckpointOneHundredSeventyTwo
import Sude.GeneratedTwinScan.S170All
import Sude.GeneratedTwinScan.S171All
import Sude.GeneratedTwinScan.S172All
import Sude.GeneratedTwinScan.S173All
import Sude.GeneratedTwinScan.S174All
import Sude.GeneratedTwinScan.S175All
import Sude.GeneratedTwinScan.S176All
import Sude.GeneratedTwinScan.S177All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred seventy-eight adjacent low segments contain exactly 1,417,490 lower endpoints. -/
theorem finiteTwinFirstOneHundredSeventyEightSegments : (twinPrimeSegment 45 373293101).card = 1417490 := by
  have h170 : (twinPrimeSegment 45 358613037).card = 1367683 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 356515885)
      (by decide : 356515885 ≤ 358613037) finiteTwinFirstOneHundredSeventySegments GeneratedTwinScan.S170All.total
  have h171 : (twinPrimeSegment 45 360710189).card = 1374743 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 358613037)
      (by decide : 358613037 ≤ 360710189) h170 GeneratedTwinScan.S171All.total
  have h172 : (twinPrimeSegment 45 362807341).card = 1381836 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 360710189)
      (by decide : 360710189 ≤ 362807341) h171 GeneratedTwinScan.S172All.total
  have h173 : (twinPrimeSegment 45 364904493).card = 1389093 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 362807341)
      (by decide : 362807341 ≤ 364904493) h172 GeneratedTwinScan.S173All.total
  have h174 : (twinPrimeSegment 45 367001645).card = 1396185 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 364904493)
      (by decide : 364904493 ≤ 367001645) h173 GeneratedTwinScan.S174All.total
  have h175 : (twinPrimeSegment 45 369098797).card = 1403234 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 367001645)
      (by decide : 367001645 ≤ 369098797) h174 GeneratedTwinScan.S175All.total
  have h176 : (twinPrimeSegment 45 371195949).card = 1410354 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 369098797)
      (by decide : 369098797 ≤ 371195949) h175 GeneratedTwinScan.S176All.total
  have h177 : (twinPrimeSegment 45 373293101).card = 1417490 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 371195949)
      (by decide : 371195949 ≤ 373293101) h176 GeneratedTwinScan.S177All.total
  exact h177

/-- One hundred seventy-eight low segments, two checked middle segments and the separate
high-end block give 1,431,148 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1431148 : 1431148 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 373293101
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
  have hlo : lo.card = 1417490 := finiteTwinFirstOneHundredSeventyEightSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
