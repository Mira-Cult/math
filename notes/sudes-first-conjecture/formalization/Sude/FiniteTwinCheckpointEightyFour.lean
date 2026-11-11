import Sude.FiniteTwinCheckpointSeventySix
import Sude.GeneratedTwinScan.S074All
import Sude.GeneratedTwinScan.S075All
import Sude.GeneratedTwinScan.S076All
import Sude.GeneratedTwinScan.S077All
import Sude.GeneratedTwinScan.S078All
import Sude.GeneratedTwinScan.S079All
import Sude.GeneratedTwinScan.S080All
import Sude.GeneratedTwinScan.S081All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Eighty-two adjacent low segments contain exactly 711,278 lower endpoints. -/
theorem finiteTwinFirstEightyTwoSegments : (twinPrimeSegment 45 171966509).card = 711278 := by
  have h74 : (twinPrimeSegment 45 157286445).card = 657424 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 155189293)
      (by decide : 155189293 ≤ 157286445) finiteTwinFirstSeventyFourSegments GeneratedTwinScan.S074All.total
  have h75 : (twinPrimeSegment 45 159383597).card = 665274 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 157286445)
      (by decide : 157286445 ≤ 159383597) h74 GeneratedTwinScan.S075All.total
  have h76 : (twinPrimeSegment 45 161480749).card = 672839 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 159383597)
      (by decide : 159383597 ≤ 161480749) h75 GeneratedTwinScan.S076All.total
  have h77 : (twinPrimeSegment 45 163577901).card = 680490 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 161480749)
      (by decide : 161480749 ≤ 163577901) h76 GeneratedTwinScan.S077All.total
  have h78 : (twinPrimeSegment 45 165675053).card = 688182 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 163577901)
      (by decide : 163577901 ≤ 165675053) h77 GeneratedTwinScan.S078All.total
  have h79 : (twinPrimeSegment 45 167772205).card = 695930 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 165675053)
      (by decide : 165675053 ≤ 167772205) h78 GeneratedTwinScan.S079All.total
  have h80 : (twinPrimeSegment 45 169869357).card = 703619 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 167772205)
      (by decide : 167772205 ≤ 169869357) h79 GeneratedTwinScan.S080All.total
  have h81 : (twinPrimeSegment 45 171966509).card = 711278 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 169869357)
      (by decide : 169869357 ≤ 171966509) h80 GeneratedTwinScan.S081All.total
  exact h81

/-- Eighty-two low segments, two checked middle segments and the separate
high-end block give 724,936 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_724936 : 724936 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 171966509
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
  have hlo : lo.card = 711278 := finiteTwinFirstEightyTwoSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
