import Sude.FiniteTwinCheckpointTwoHundredTwenty
import Sude.GeneratedTwinScan.S218All
import Sude.GeneratedTwinScan.S219All
import Sude.GeneratedTwinScan.S220All
import Sude.GeneratedTwinScan.S221All
import Sude.GeneratedTwinScan.S222All
import Sude.GeneratedTwinScan.S223All
import Sude.GeneratedTwinScan.S224All
import Sude.GeneratedTwinScan.S225All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Two hundred twenty-six adjacent low segments contain exactly 1,754,467 lower endpoints. -/
theorem finiteTwinFirstTwoHundredTwentySixSegments : (twinPrimeSegment 45 473956397).card = 1754467 := by
  have h218 : (twinPrimeSegment 45 459276333).card = 1706048 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 457179181)
      (by decide : 457179181 ≤ 459276333) finiteTwinFirstTwoHundredEighteenSegments GeneratedTwinScan.S218All.total
  have h219 : (twinPrimeSegment 45 461373485).card = 1712964 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 459276333)
      (by decide : 459276333 ≤ 461373485) h218 GeneratedTwinScan.S219All.total
  have h220 : (twinPrimeSegment 45 463470637).card = 1719868 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 461373485)
      (by decide : 461373485 ≤ 463470637) h219 GeneratedTwinScan.S220All.total
  have h221 : (twinPrimeSegment 45 465567789).card = 1726722 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 463470637)
      (by decide : 463470637 ≤ 465567789) h220 GeneratedTwinScan.S221All.total
  have h222 : (twinPrimeSegment 45 467664941).card = 1733775 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 465567789)
      (by decide : 465567789 ≤ 467664941) h221 GeneratedTwinScan.S222All.total
  have h223 : (twinPrimeSegment 45 469762093).card = 1740601 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 467664941)
      (by decide : 467664941 ≤ 469762093) h222 GeneratedTwinScan.S223All.total
  have h224 : (twinPrimeSegment 45 471859245).card = 1747607 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 469762093)
      (by decide : 469762093 ≤ 471859245) h223 GeneratedTwinScan.S224All.total
  have h225 : (twinPrimeSegment 45 473956397).card = 1754467 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 471859245)
      (by decide : 471859245 ≤ 473956397) h224 GeneratedTwinScan.S225All.total
  exact h225

/-- Two hundred twenty-six low segments, two checked middle segments and the separate
high-end block give 1,768,125 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1768125 : 1768125 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 473956397
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
  have hlo : lo.card = 1754467 := finiteTwinFirstTwoHundredTwentySixSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
