import Sude.FiniteTwinLowActive65536
import Sude.FiniteTwinHighActive16384
import Sude.GeneratedTwinScan.S000C01

/-! Disjoint kernel-checked contributions to the full FT matching. -/
namespace Sude
noncomputable section

/-- The independently checked low and high blocks contain at least 1,611
source seed pairs. This does not assert the full FT population. -/
theorem finiteTwinSeeds_at_least_1611 : 1611 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 131117
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
  have hlo : lo.card = 1521 := finiteTwinLow65536_mathematical
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

/-- Two adjacent verified low-end groups have 2,674 pairs. -/
theorem finiteTwinLow131072_mathematical : (twinPrimeSegment 45 262189).card = 2674 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 131117) (by decide : 131117 ≤ 262189)
    finiteTwinLow65536_mathematical Sude.GeneratedTwinScan.S000C01.total

/-- The checked low and high blocks give a stronger partial FT lower bound. -/
theorem finiteTwinSeeds_at_least_2764 : 2764 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 262189
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
  have hlo : lo.card = 2674 := finiteTwinLow131072_mathematical
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
