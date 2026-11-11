import Sude.FiniteTwinCheckpointEightyFour
import Sude.GeneratedTwinScan.S082All
import Sude.GeneratedTwinScan.S083All
import Sude.GeneratedTwinScan.S084All
import Sude.GeneratedTwinScan.S085All
import Sude.GeneratedTwinScan.S086All
import Sude.GeneratedTwinScan.S087All
import Sude.GeneratedTwinScan.S088All
import Sude.GeneratedTwinScan.S089All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Ninety adjacent low segments contain exactly 772,464 lower endpoints. -/
theorem finiteTwinFirstNinetySegments : (twinPrimeSegment 45 188743725).card = 772464 := by
  have h82 : (twinPrimeSegment 45 174063661).card = 718900 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 171966509)
      (by decide : 171966509 ≤ 174063661) finiteTwinFirstEightyTwoSegments GeneratedTwinScan.S082All.total
  have h83 : (twinPrimeSegment 45 176160813).card = 726640 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 174063661)
      (by decide : 174063661 ≤ 176160813) h82 GeneratedTwinScan.S083All.total
  have h84 : (twinPrimeSegment 45 178257965).card = 734320 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 176160813)
      (by decide : 176160813 ≤ 178257965) h83 GeneratedTwinScan.S084All.total
  have h85 : (twinPrimeSegment 45 180355117).card = 741971 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 178257965)
      (by decide : 178257965 ≤ 180355117) h84 GeneratedTwinScan.S085All.total
  have h86 : (twinPrimeSegment 45 182452269).card = 749513 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 180355117)
      (by decide : 180355117 ≤ 182452269) h85 GeneratedTwinScan.S086All.total
  have h87 : (twinPrimeSegment 45 184549421).card = 757113 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 182452269)
      (by decide : 182452269 ≤ 184549421) h86 GeneratedTwinScan.S087All.total
  have h88 : (twinPrimeSegment 45 186646573).card = 764762 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 184549421)
      (by decide : 184549421 ≤ 186646573) h87 GeneratedTwinScan.S088All.total
  have h89 : (twinPrimeSegment 45 188743725).card = 772464 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 186646573)
      (by decide : 186646573 ≤ 188743725) h88 GeneratedTwinScan.S089All.total
  exact h89

/-- Ninety low segments, two checked middle segments and the separate
high-end block give 786,122 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_786122 : 786122 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 188743725
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
  have hlo : lo.card = 772464 := finiteTwinFirstNinetySegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
