import Sude.FiniteTwinCheckpointTwoHundredFour
import Sude.GeneratedTwinScan.S202All
import Sude.GeneratedTwinScan.S203All
import Sude.GeneratedTwinScan.S204All
import Sude.GeneratedTwinScan.S205All
import Sude.GeneratedTwinScan.S206All
import Sude.GeneratedTwinScan.S207All
import Sude.GeneratedTwinScan.S208All
import Sude.GeneratedTwinScan.S209All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- Two hundred ten adjacent low segments contain exactly 1,643,210 lower endpoints. -/
theorem finiteTwinFirstTwoHundredTenSegments : (twinPrimeSegment 45 440401965).card = 1643210 := by
  have h202 : (twinPrimeSegment 45 425721901).card = 1594104 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 423624749)
      (by decide : 423624749 ≤ 425721901) finiteTwinFirstTwoHundredTwoSegments GeneratedTwinScan.S202All.total
  have h203 : (twinPrimeSegment 45 427819053).card = 1601072 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 425721901)
      (by decide : 425721901 ≤ 427819053) h202 GeneratedTwinScan.S203All.total
  have h204 : (twinPrimeSegment 45 429916205).card = 1608021 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 427819053)
      (by decide : 427819053 ≤ 429916205) h203 GeneratedTwinScan.S204All.total
  have h205 : (twinPrimeSegment 45 432013357).card = 1615002 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 429916205)
      (by decide : 429916205 ≤ 432013357) h204 GeneratedTwinScan.S205All.total
  have h206 : (twinPrimeSegment 45 434110509).card = 1622009 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 432013357)
      (by decide : 432013357 ≤ 434110509) h205 GeneratedTwinScan.S206All.total
  have h207 : (twinPrimeSegment 45 436207661).card = 1629104 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 434110509)
      (by decide : 434110509 ≤ 436207661) h206 GeneratedTwinScan.S207All.total
  have h208 : (twinPrimeSegment 45 438304813).card = 1636172 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 436207661)
      (by decide : 436207661 ≤ 438304813) h207 GeneratedTwinScan.S208All.total
  have h209 : (twinPrimeSegment 45 440401965).card = 1643210 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 438304813)
      (by decide : 438304813 ≤ 440401965) h208 GeneratedTwinScan.S209All.total
  exact h209

/-- Two hundred ten low segments, two checked middle segments and the separate
high-end block give 1,656,868 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1656868 : 1656868 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 440401965
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
  have hlo : lo.card = 1643210 := finiteTwinFirstTwoHundredTenSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
