import Sude.FiniteTwinCheckpointOneHundredEight
import Sude.GeneratedTwinScan.S106All
import Sude.GeneratedTwinScan.S107All
import Sude.GeneratedTwinScan.S108All
import Sude.GeneratedTwinScan.S109All
import Sude.GeneratedTwinScan.S110All
import Sude.GeneratedTwinScan.S111All
import Sude.GeneratedTwinScan.S112All
import Sude.GeneratedTwinScan.S113All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred fourteen adjacent low segments contain exactly 952,869 lower endpoints. -/
theorem finiteTwinFirstOneHundredFourteenSegments : (twinPrimeSegment 45 239075373).card = 952869 := by
  have h106 : (twinPrimeSegment 45 224395309).card = 900834 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 222298157)
      (by decide : 222298157 ≤ 224395309) finiteTwinFirstOneHundredSixSegments GeneratedTwinScan.S106All.total
  have h107 : (twinPrimeSegment 45 226492461).card = 908191 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 224395309)
      (by decide : 224395309 ≤ 226492461) h106 GeneratedTwinScan.S107All.total
  have h108 : (twinPrimeSegment 45 228589613).card = 915552 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 226492461)
      (by decide : 226492461 ≤ 228589613) h107 GeneratedTwinScan.S108All.total
  have h109 : (twinPrimeSegment 45 230686765).card = 922997 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 228589613)
      (by decide : 228589613 ≤ 230686765) h108 GeneratedTwinScan.S109All.total
  have h110 : (twinPrimeSegment 45 232783917).card = 930339 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 230686765)
      (by decide : 230686765 ≤ 232783917) h109 GeneratedTwinScan.S110All.total
  have h111 : (twinPrimeSegment 45 234881069).card = 937776 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 232783917)
      (by decide : 232783917 ≤ 234881069) h110 GeneratedTwinScan.S111All.total
  have h112 : (twinPrimeSegment 45 236978221).card = 945349 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 234881069)
      (by decide : 234881069 ≤ 236978221) h111 GeneratedTwinScan.S112All.total
  have h113 : (twinPrimeSegment 45 239075373).card = 952869 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 236978221)
      (by decide : 236978221 ≤ 239075373) h112 GeneratedTwinScan.S113All.total
  exact h113

/-- One hundred fourteen low segments, two checked middle segments and the separate
high-end block give 966,527 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_966527 : 966527 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 239075373
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
  have hlo : lo.card = 952869 := finiteTwinFirstOneHundredFourteenSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
