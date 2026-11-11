import Sude.FiniteTwinCheckpointTwoHundredThirtySix
import Sude.GeneratedTwinScan.S234All
import Sude.GeneratedTwinScan.S235All
import Sude.GeneratedTwinScan.S236All
import Sude.GeneratedTwinScan.S237All
import Sude.GeneratedTwinScan.S238All
import Sude.GeneratedTwinScan.S239All
import Sude.GeneratedTwinScan.S240All
import Sude.GeneratedTwinScan.S241All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Two hundred forty-two adjacent low segments contain exactly 1,864,712 lower endpoints. -/
theorem finiteTwinFirstTwoHundredFortyTwoSegments : (twinPrimeSegment 45 507510829).card = 1864712 := by
  have h234 : (twinPrimeSegment 45 492830765).card = 1816620 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 490733613)
      (by decide : 490733613 ≤ 492830765) finiteTwinFirstTwoHundredThirtyFourSegments GeneratedTwinScan.S234All.total
  have h235 : (twinPrimeSegment 45 494927917).card = 1823458 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 492830765)
      (by decide : 492830765 ≤ 494927917) h234 GeneratedTwinScan.S235All.total
  have h236 : (twinPrimeSegment 45 497025069).card = 1830360 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 494927917)
      (by decide : 494927917 ≤ 497025069) h235 GeneratedTwinScan.S236All.total
  have h237 : (twinPrimeSegment 45 499122221).card = 1837240 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 497025069)
      (by decide : 497025069 ≤ 499122221) h236 GeneratedTwinScan.S237All.total
  have h238 : (twinPrimeSegment 45 501219373).card = 1844135 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 499122221)
      (by decide : 499122221 ≤ 501219373) h237 GeneratedTwinScan.S238All.total
  have h239 : (twinPrimeSegment 45 503316525).card = 1850954 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 501219373)
      (by decide : 501219373 ≤ 503316525) h238 GeneratedTwinScan.S239All.total
  have h240 : (twinPrimeSegment 45 505413677).card = 1857830 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 503316525)
      (by decide : 503316525 ≤ 505413677) h239 GeneratedTwinScan.S240All.total
  have h241 : (twinPrimeSegment 45 507510829).card = 1864712 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 505413677)
      (by decide : 505413677 ≤ 507510829) h240 GeneratedTwinScan.S241All.total
  exact h241

/-- Two hundred forty-two low segments, two checked middle segments and the separate
high-end block give 1,878,370 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1878370 : 1878370 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 507510829
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
  have hlo : lo.card = 1864712 := finiteTwinFirstTwoHundredFortyTwoSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
