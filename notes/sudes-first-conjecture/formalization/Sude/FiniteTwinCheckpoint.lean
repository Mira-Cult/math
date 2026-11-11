import Sude.GeneratedTwinScan.S000All
import Sude.GeneratedTwinScan.S001All
import Sude.GeneratedTwinScan.S002All
import Sude.FiniteTwinHighActive16384

/-! Explicit partial FT population from three kernel-checked regions. -/
namespace Sude
noncomputable section

/-- The first two adjacent source segments contain exactly 27,989 pairs. -/
theorem finiteTwinFirstTwoSegments : (twinPrimeSegment 45 4194349).card = 27989 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 2097197)
    (by decide : 2097197 ≤ 4194349)
    GeneratedTwinScan.S000All.total GeneratedTwinScan.S001All.total

/-- The first three adjacent source segments contain exactly 39,524 pairs. -/
theorem finiteTwinFirstThreeSegments : (twinPrimeSegment 45 6291501).card = 39524 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 4194349)
    (by decide : 4194349 ≤ 6291501)
    finiteTwinFirstTwoSegments GeneratedTwinScan.S002All.total

/-- Those three segments and the separately checked high-end block provide a
partial lower bound. This is not the full FT population. -/
theorem finiteTwinSeeds_at_least_39614 : 39614 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 6291501
  let hi := twinPrimeSegment 1073709055 1073741823
  have hdis : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [lo, hi, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp hq
    omega
  have hsub : lo ∪ hi ⊆ finiteTwinSeeds := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · simp only [lo, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
      apply (mem_finiteTwinSeeds p).mpr
      exact ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
    · simp only [hi, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
      apply (mem_finiteTwinSeeds p).mpr
      exact ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at h
  have hlo : lo.card = 39524 := finiteTwinFirstThreeSegments
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
