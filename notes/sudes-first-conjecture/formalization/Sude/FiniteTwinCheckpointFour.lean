import Sude.FiniteTwinCheckpoint
import Sude.GeneratedTwinScan.S003All

/-! A fourth kernel-checked source segment strengthens the partial bound. -/
namespace Sude
noncomputable section

/-- The first four adjacent source segments contain exactly 50,633 pairs. -/
theorem finiteTwinFirstFourSegments : (twinPrimeSegment 45 8388653).card = 50633 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 6291501)
    (by decide : 6291501 ≤ 8388653)
    finiteTwinFirstThreeSegments GeneratedTwinScan.S003All.total

/-- The four low segments and checked high-end block give a partial bound. -/
theorem finiteTwinSeeds_at_least_50723 : 50723 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 8388653
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
  have hlo : lo.card = 50633 := finiteTwinFirstFourSegments
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega


end
end Sude
