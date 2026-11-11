import Sude.FiniteTwinCheckpointNinetyTwo
import Sude.GeneratedTwinScan.S090All
import Sude.GeneratedTwinScan.S091All
import Sude.GeneratedTwinScan.S092All
import Sude.GeneratedTwinScan.S093All
import Sude.GeneratedTwinScan.S094All
import Sude.GeneratedTwinScan.S095All
import Sude.GeneratedTwinScan.S096All
import Sude.GeneratedTwinScan.S097All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Ninety-eight adjacent low segments contain exactly 833,149 lower endpoints. -/
theorem finiteTwinFirstNinetyEightSegments : (twinPrimeSegment 45 205520941).card = 833149 := by
  have h90 : (twinPrimeSegment 45 190840877).card = 780050 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 188743725)
      (by decide : 188743725 ≤ 190840877) finiteTwinFirstNinetySegments GeneratedTwinScan.S090All.total
  have h91 : (twinPrimeSegment 45 192938029).card = 787625 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 190840877)
      (by decide : 190840877 ≤ 192938029) h90 GeneratedTwinScan.S091All.total
  have h92 : (twinPrimeSegment 45 195035181).card = 795288 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 192938029)
      (by decide : 192938029 ≤ 195035181) h91 GeneratedTwinScan.S092All.total
  have h93 : (twinPrimeSegment 45 197132333).card = 802849 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 195035181)
      (by decide : 195035181 ≤ 197132333) h92 GeneratedTwinScan.S093All.total
  have h94 : (twinPrimeSegment 45 199229485).card = 810460 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 197132333)
      (by decide : 197132333 ≤ 199229485) h93 GeneratedTwinScan.S094All.total
  have h95 : (twinPrimeSegment 45 201326637).card = 818143 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 199229485)
      (by decide : 199229485 ≤ 201326637) h94 GeneratedTwinScan.S095All.total
  have h96 : (twinPrimeSegment 45 203423789).card = 825583 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 201326637)
      (by decide : 201326637 ≤ 203423789) h95 GeneratedTwinScan.S096All.total
  have h97 : (twinPrimeSegment 45 205520941).card = 833149 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 203423789)
      (by decide : 203423789 ≤ 205520941) h96 GeneratedTwinScan.S097All.total
  exact h97

/-- Ninety-eight low segments, two checked middle segments and the separate
high-end block give 846,807 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_846807 : 846807 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 205520941
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
  have hlo : lo.card = 833149 := finiteTwinFirstNinetyEightSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
