import Sude.FiniteTwinCheckpointOneHundredFortyEight
import Sude.GeneratedTwinScan.S146All
import Sude.GeneratedTwinScan.S147All
import Sude.GeneratedTwinScan.S148All
import Sude.GeneratedTwinScan.S149All
import Sude.GeneratedTwinScan.S150All
import Sude.GeneratedTwinScan.S151All
import Sude.GeneratedTwinScan.S152All
import Sude.GeneratedTwinScan.S153All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred fifty-four adjacent low segments contain exactly 1,245,881 lower endpoints. -/
theorem finiteTwinFirstOneHundredFiftyFourSegments : (twinPrimeSegment 45 322961453).card = 1245881 := by
  have h146 : (twinPrimeSegment 45 308281389).card = 1195265 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 306184237)
      (by decide : 306184237 ≤ 308281389) finiteTwinFirstOneHundredFortySixSegments GeneratedTwinScan.S146All.total
  have h147 : (twinPrimeSegment 45 310378541).card = 1202477 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 308281389)
      (by decide : 308281389 ≤ 310378541) h146 GeneratedTwinScan.S147All.total
  have h148 : (twinPrimeSegment 45 312475693).card = 1209768 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 310378541)
      (by decide : 310378541 ≤ 312475693) h147 GeneratedTwinScan.S148All.total
  have h149 : (twinPrimeSegment 45 314572845).card = 1216933 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 312475693)
      (by decide : 312475693 ≤ 314572845) h148 GeneratedTwinScan.S149All.total
  have h150 : (twinPrimeSegment 45 316669997).card = 1224073 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 314572845)
      (by decide : 314572845 ≤ 316669997) h149 GeneratedTwinScan.S150All.total
  have h151 : (twinPrimeSegment 45 318767149).card = 1231392 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 316669997)
      (by decide : 316669997 ≤ 318767149) h150 GeneratedTwinScan.S151All.total
  have h152 : (twinPrimeSegment 45 320864301).card = 1238691 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 318767149)
      (by decide : 318767149 ≤ 320864301) h151 GeneratedTwinScan.S152All.total
  have h153 : (twinPrimeSegment 45 322961453).card = 1245881 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 320864301)
      (by decide : 320864301 ≤ 322961453) h152 GeneratedTwinScan.S153All.total
  exact h153

/-- One hundred fifty-four low segments, two checked middle segments and the separate
high-end block give 1,259,539 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1259539 : 1259539 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 322961453
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
  have hlo : lo.card = 1245881 := finiteTwinFirstOneHundredFiftyFourSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
