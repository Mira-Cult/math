import Sude.FiniteTwinCheckpointOneHundredEightyEight
import Sude.GeneratedTwinScan.S186All
import Sude.GeneratedTwinScan.S187All
import Sude.GeneratedTwinScan.S188All
import Sude.GeneratedTwinScan.S189All
import Sude.GeneratedTwinScan.S190All
import Sude.GeneratedTwinScan.S191All
import Sude.GeneratedTwinScan.S192All
import Sude.GeneratedTwinScan.S193All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred ninety-four adjacent low segments contain exactly 1,530,710 lower endpoints. -/
theorem finiteTwinFirstOneHundredNinetyFourSegments : (twinPrimeSegment 45 406847533).card = 1530710 := by
  have h186 : (twinPrimeSegment 45 392167469).card = 1481381 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 390070317)
      (by decide : 390070317 ≤ 392167469) finiteTwinFirstOneHundredEightySixSegments GeneratedTwinScan.S186All.total
  have h187 : (twinPrimeSegment 45 394264621).card = 1488437 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 392167469)
      (by decide : 392167469 ≤ 394264621) h186 GeneratedTwinScan.S187All.total
  have h188 : (twinPrimeSegment 45 396361773).card = 1495475 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 394264621)
      (by decide : 394264621 ≤ 396361773) h187 GeneratedTwinScan.S188All.total
  have h189 : (twinPrimeSegment 45 398458925).card = 1502556 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 396361773)
      (by decide : 396361773 ≤ 398458925) h188 GeneratedTwinScan.S189All.total
  have h190 : (twinPrimeSegment 45 400556077).card = 1509571 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 398458925)
      (by decide : 398458925 ≤ 400556077) h189 GeneratedTwinScan.S190All.total
  have h191 : (twinPrimeSegment 45 402653229).card = 1516639 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 400556077)
      (by decide : 400556077 ≤ 402653229) h190 GeneratedTwinScan.S191All.total
  have h192 : (twinPrimeSegment 45 404750381).card = 1523714 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 402653229)
      (by decide : 402653229 ≤ 404750381) h191 GeneratedTwinScan.S192All.total
  have h193 : (twinPrimeSegment 45 406847533).card = 1530710 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 404750381)
      (by decide : 404750381 ≤ 406847533) h192 GeneratedTwinScan.S193All.total
  exact h193

/-- One hundred ninety-four low segments, two checked middle segments and the separate
high-end block give 1,544,368 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1544368 : 1544368 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 406847533
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
  have hlo : lo.card = 1530710 := finiteTwinFirstOneHundredNinetyFourSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
