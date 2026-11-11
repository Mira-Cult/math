import Sude.FiniteTwinCheckpointOneHundredForty
import Sude.GeneratedTwinScan.S138All
import Sude.GeneratedTwinScan.S139All
import Sude.GeneratedTwinScan.S140All
import Sude.GeneratedTwinScan.S141All
import Sude.GeneratedTwinScan.S142All
import Sude.GeneratedTwinScan.S143All
import Sude.GeneratedTwinScan.S144All
import Sude.GeneratedTwinScan.S145All

/-! Add eight adjacent checked intervals to the finite twin-seed population. -/
namespace Sude
noncomputable section

/-- One hundred forty-six adjacent low segments contain exactly 1,187,923 lower endpoints. -/
theorem finiteTwinFirstOneHundredFortySixSegments : (twinPrimeSegment 45 306184237).card = 1187923 := by
  have h138 : (twinPrimeSegment 45 291504173).card = 1137010 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 289407021)
      (by decide : 289407021 ≤ 291504173) finiteTwinFirstOneHundredThirtyEightSegments GeneratedTwinScan.S138All.total
  have h139 : (twinPrimeSegment 45 293601325).card = 1144348 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 291504173)
      (by decide : 291504173 ≤ 293601325) h138 GeneratedTwinScan.S139All.total
  have h140 : (twinPrimeSegment 45 295698477).card = 1151693 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 293601325)
      (by decide : 293601325 ≤ 295698477) h139 GeneratedTwinScan.S140All.total
  have h141 : (twinPrimeSegment 45 297795629).card = 1158916 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 295698477)
      (by decide : 295698477 ≤ 297795629) h140 GeneratedTwinScan.S141All.total
  have h142 : (twinPrimeSegment 45 299892781).card = 1166105 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 297795629)
      (by decide : 297795629 ≤ 299892781) h141 GeneratedTwinScan.S142All.total
  have h143 : (twinPrimeSegment 45 301989933).card = 1173331 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 299892781)
      (by decide : 299892781 ≤ 301989933) h142 GeneratedTwinScan.S143All.total
  have h144 : (twinPrimeSegment 45 304087085).card = 1180534 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 301989933)
      (by decide : 301989933 ≤ 304087085) h143 GeneratedTwinScan.S144All.total
  have h145 : (twinPrimeSegment 45 306184237).card = 1187923 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 304087085)
      (by decide : 304087085 ≤ 306184237) h144 GeneratedTwinScan.S145All.total
  exact h145

/-- One hundred forty-six low segments, two checked middle segments and the separate
high-end block give 1,201,581 distinct finite twin-prime seeds. -/
theorem finiteTwinSeeds_at_least_1201581 : 1201581 ≤ finiteTwinSeeds.card := by
  let lo := twinPrimeSegment 45 306184237
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
  have hlo : lo.card = 1187923 := finiteTwinFirstOneHundredFortySixSegments
  have hmid : mid.card = 13568 := by
    simpa [mid] using combineTwinPrimeSegments
      (by decide : 538968109 ≤ 541065261) (by decide : 541065261 ≤ 543162413)
      GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total
  have hhi : hi.card = 90 := finiteTwinHighActive16384_mathematical
  omega

end
end Sude
