import Sude.FiniteTwinCheckpointOneHundredTwentyFour
import Sude.GeneratedTwinScan.S122All
import Sude.GeneratedTwinScan.S123All
import Sude.GeneratedTwinScan.S124All
import Sude.GeneratedTwinScan.S125All
import Sude.GeneratedTwinScan.S126All
import Sude.GeneratedTwinScan.S127All
import Sude.GeneratedTwinScan.S128All
import Sude.GeneratedTwinScan.S129All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred thirty adjacent low segments contain exactly 1,070,984 lower endpoints. -/
theorem finiteTwinFirstOneHundredThirtySegments : (twinPrimeSegment 45 272629805).card = 1070984 := by
  have h122 : (twinPrimeSegment 45 257949741).card = 1019429 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 255852589)
      (by decide : 255852589 ≤ 257949741) finiteTwinFirstOneHundredTwentyTwoSegments GeneratedTwinScan.S122All.total
  have h123 : (twinPrimeSegment 45 260046893).card = 1026758 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 257949741)
      (by decide : 257949741 ≤ 260046893) h122 GeneratedTwinScan.S123All.total
  have h124 : (twinPrimeSegment 45 262144045).card = 1034333 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 260046893)
      (by decide : 260046893 ≤ 262144045) h123 GeneratedTwinScan.S124All.total
  have h125 : (twinPrimeSegment 45 264241197).card = 1041653 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 262144045)
      (by decide : 262144045 ≤ 264241197) h124 GeneratedTwinScan.S125All.total
  have h126 : (twinPrimeSegment 45 266338349).card = 1049052 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 264241197)
      (by decide : 264241197 ≤ 266338349) h125 GeneratedTwinScan.S126All.total
  have h127 : (twinPrimeSegment 45 268435501).card = 1056275 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 266338349)
      (by decide : 266338349 ≤ 268435501) h126 GeneratedTwinScan.S127All.total
  have h128 : (twinPrimeSegment 45 270532653).card = 1063632 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 268435501)
      (by decide : 268435501 ≤ 270532653) h127 GeneratedTwinScan.S128All.total
  have h129 : (twinPrimeSegment 45 272629805).card = 1070984 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 270532653)
      (by decide : 270532653 ≤ 272629805) h128 GeneratedTwinScan.S129All.total
  exact h129

/-- One hundred thirty low segments, two checked middle segments and the separate
high-end block give 1,084,642 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1084642 : 1084642 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 272629805
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
  have hlo : lo.card = 1070984 := finiteTwinFirstOneHundredThirtySegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
