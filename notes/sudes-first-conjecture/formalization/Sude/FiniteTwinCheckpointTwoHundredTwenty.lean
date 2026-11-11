import Sude.FiniteTwinCheckpointTwoHundredTwelve
import Sude.GeneratedTwinScan.S210All
import Sude.GeneratedTwinScan.S211All
import Sude.GeneratedTwinScan.S212All
import Sude.GeneratedTwinScan.S213All
import Sude.GeneratedTwinScan.S214All
import Sude.GeneratedTwinScan.S215All
import Sude.GeneratedTwinScan.S216All
import Sude.GeneratedTwinScan.S217All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Two hundred eighteen adjacent low segments contain exactly 1,699,099 lower endpoints. -/
theorem finiteTwinFirstTwoHundredEighteenSegments : (twinPrimeSegment 45 457179181).card = 1699099 := by
  have h210 : (twinPrimeSegment 45 442499117).card = 1650174 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 440401965)
      (by decide : 440401965 ≤ 442499117) finiteTwinFirstTwoHundredTenSegments GeneratedTwinScan.S210All.total
  have h211 : (twinPrimeSegment 45 444596269).card = 1657157 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 442499117)
      (by decide : 442499117 ≤ 444596269) h210 GeneratedTwinScan.S211All.total
  have h212 : (twinPrimeSegment 45 446693421).card = 1664176 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 444596269)
      (by decide : 444596269 ≤ 446693421) h211 GeneratedTwinScan.S212All.total
  have h213 : (twinPrimeSegment 45 448790573).card = 1671138 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 446693421)
      (by decide : 446693421 ≤ 448790573) h212 GeneratedTwinScan.S213All.total
  have h214 : (twinPrimeSegment 45 450887725).card = 1678129 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 448790573)
      (by decide : 448790573 ≤ 450887725) h213 GeneratedTwinScan.S214All.total
  have h215 : (twinPrimeSegment 45 452984877).card = 1685049 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 450887725)
      (by decide : 450887725 ≤ 452984877) h214 GeneratedTwinScan.S215All.total
  have h216 : (twinPrimeSegment 45 455082029).card = 1692084 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 452984877)
      (by decide : 452984877 ≤ 455082029) h215 GeneratedTwinScan.S216All.total
  have h217 : (twinPrimeSegment 45 457179181).card = 1699099 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 455082029)
      (by decide : 455082029 ≤ 457179181) h216 GeneratedTwinScan.S217All.total
  exact h217

/-- Two hundred eighteen low segments, two checked middle segments and the separate
high-end block give 1,712,757 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1712757 : 1712757 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 457179181
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
  have hlo : lo.card = 1699099 := finiteTwinFirstTwoHundredEighteenSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
