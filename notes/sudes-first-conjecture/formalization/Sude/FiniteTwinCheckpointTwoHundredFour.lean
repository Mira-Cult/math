import Sude.FiniteTwinCheckpointOneHundredNinetySix
import Sude.GeneratedTwinScan.S194All
import Sude.GeneratedTwinScan.S195All
import Sude.GeneratedTwinScan.S196All
import Sude.GeneratedTwinScan.S197All
import Sude.GeneratedTwinScan.S198All
import Sude.GeneratedTwinScan.S199All
import Sude.GeneratedTwinScan.S200All
import Sude.GeneratedTwinScan.S201All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Two hundred two adjacent low segments contain exactly 1,587,113 lower endpoints. -/
theorem finiteTwinFirstTwoHundredTwoSegments : (twinPrimeSegment 45 423624749).card = 1587113 := by
  have h194 : (twinPrimeSegment 45 408944685).card = 1537748 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 406847533)
      (by decide : 406847533 ≤ 408944685) finiteTwinFirstOneHundredNinetyFourSegments GeneratedTwinScan.S194All.total
  have h195 : (twinPrimeSegment 45 411041837).card = 1544764 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 408944685)
      (by decide : 408944685 ≤ 411041837) h194 GeneratedTwinScan.S195All.total
  have h196 : (twinPrimeSegment 45 413138989).card = 1551787 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 411041837)
      (by decide : 411041837 ≤ 413138989) h195 GeneratedTwinScan.S196All.total
  have h197 : (twinPrimeSegment 45 415236141).card = 1558770 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 413138989)
      (by decide : 413138989 ≤ 415236141) h196 GeneratedTwinScan.S197All.total
  have h198 : (twinPrimeSegment 45 417333293).card = 1565821 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 415236141)
      (by decide : 415236141 ≤ 417333293) h197 GeneratedTwinScan.S198All.total
  have h199 : (twinPrimeSegment 45 419430445).card = 1572941 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 417333293)
      (by decide : 417333293 ≤ 419430445) h198 GeneratedTwinScan.S199All.total
  have h200 : (twinPrimeSegment 45 421527597).card = 1580072 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 419430445)
      (by decide : 419430445 ≤ 421527597) h199 GeneratedTwinScan.S200All.total
  have h201 : (twinPrimeSegment 45 423624749).card = 1587113 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 421527597)
      (by decide : 421527597 ≤ 423624749) h200 GeneratedTwinScan.S201All.total
  exact h201

/-- Two hundred two low segments, two checked middle segments and the separate
high-end block give 1,600,771 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1600771 : 1600771 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 423624749
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
  have hlo : lo.card = 1587113 := finiteTwinFirstTwoHundredTwoSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
