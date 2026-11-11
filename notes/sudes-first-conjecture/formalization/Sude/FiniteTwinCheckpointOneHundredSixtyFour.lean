import Sude.FiniteTwinCheckpointOneHundredFiftySix
import Sude.GeneratedTwinScan.S154All
import Sude.GeneratedTwinScan.S155All
import Sude.GeneratedTwinScan.S156All
import Sude.GeneratedTwinScan.S157All
import Sude.GeneratedTwinScan.S158All
import Sude.GeneratedTwinScan.S159All
import Sude.GeneratedTwinScan.S160All
import Sude.GeneratedTwinScan.S161All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred sixty-two adjacent low segments contain exactly 1,303,498 lower endpoints. -/
theorem finiteTwinFirstOneHundredSixtyTwoSegments : (twinPrimeSegment 45 339738669).card = 1303498 := by
  have h154 : (twinPrimeSegment 45 325058605).card = 1253203 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 322961453)
      (by decide : 322961453 ≤ 325058605) finiteTwinFirstOneHundredFiftyFourSegments GeneratedTwinScan.S154All.total
  have h155 : (twinPrimeSegment 45 327155757).card = 1260427 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 325058605)
      (by decide : 325058605 ≤ 327155757) h154 GeneratedTwinScan.S155All.total
  have h156 : (twinPrimeSegment 45 329252909).card = 1267570 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 327155757)
      (by decide : 327155757 ≤ 329252909) h155 GeneratedTwinScan.S156All.total
  have h157 : (twinPrimeSegment 45 331350061).card = 1274734 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 329252909)
      (by decide : 329252909 ≤ 331350061) h156 GeneratedTwinScan.S157All.total
  have h158 : (twinPrimeSegment 45 333447213).card = 1281980 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 331350061)
      (by decide : 331350061 ≤ 333447213) h157 GeneratedTwinScan.S158All.total
  have h159 : (twinPrimeSegment 45 335544365).card = 1289187 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 333447213)
      (by decide : 333447213 ≤ 335544365) h158 GeneratedTwinScan.S159All.total
  have h160 : (twinPrimeSegment 45 337641517).card = 1296393 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 335544365)
      (by decide : 335544365 ≤ 337641517) h159 GeneratedTwinScan.S160All.total
  have h161 : (twinPrimeSegment 45 339738669).card = 1303498 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 337641517)
      (by decide : 337641517 ≤ 339738669) h160 GeneratedTwinScan.S161All.total
  exact h161

/-- One hundred sixty-two low segments, two checked middle segments and the separate
high-end block give 1,317,156 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1317156 : 1317156 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 339738669
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
  have hlo : lo.card = 1303498 := finiteTwinFirstOneHundredSixtyTwoSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
