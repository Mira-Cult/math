import Sude.FiniteTwinCheckpointOneHundredEighty
import Sude.GeneratedTwinScan.S178All
import Sude.GeneratedTwinScan.S179All
import Sude.GeneratedTwinScan.S180All
import Sude.GeneratedTwinScan.S181All
import Sude.GeneratedTwinScan.S182All
import Sude.GeneratedTwinScan.S183All
import Sude.GeneratedTwinScan.S184All
import Sude.GeneratedTwinScan.S185All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred eighty-six adjacent low segments contain exactly 1,474,310 lower endpoints. -/
theorem finiteTwinFirstOneHundredEightySixSegments : (twinPrimeSegment 45 390070317).card = 1474310 := by
  have h178 : (twinPrimeSegment 45 375390253).card = 1424620 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 373293101)
      (by decide : 373293101 ≤ 375390253) finiteTwinFirstOneHundredSeventyEightSegments GeneratedTwinScan.S178All.total
  have h179 : (twinPrimeSegment 45 377487405).card = 1431699 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 375390253)
      (by decide : 375390253 ≤ 377487405) h178 GeneratedTwinScan.S179All.total
  have h180 : (twinPrimeSegment 45 379584557).card = 1438743 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 377487405)
      (by decide : 377487405 ≤ 379584557) h179 GeneratedTwinScan.S180All.total
  have h181 : (twinPrimeSegment 45 381681709).card = 1445964 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 379584557)
      (by decide : 379584557 ≤ 381681709) h180 GeneratedTwinScan.S181All.total
  have h182 : (twinPrimeSegment 45 383778861).card = 1453163 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 381681709)
      (by decide : 381681709 ≤ 383778861) h181 GeneratedTwinScan.S182All.total
  have h183 : (twinPrimeSegment 45 385876013).card = 1460219 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 383778861)
      (by decide : 383778861 ≤ 385876013) h182 GeneratedTwinScan.S183All.total
  have h184 : (twinPrimeSegment 45 387973165).card = 1467308 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 385876013)
      (by decide : 385876013 ≤ 387973165) h183 GeneratedTwinScan.S184All.total
  have h185 : (twinPrimeSegment 45 390070317).card = 1474310 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 387973165)
      (by decide : 387973165 ≤ 390070317) h184 GeneratedTwinScan.S185All.total
  exact h185

/-- One hundred eighty-six low segments, two checked middle segments and the separate
high-end block give 1,487,968 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1487968 : 1487968 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 390070317
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
  have hlo : lo.card = 1474310 := finiteTwinFirstOneHundredEightySixSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
