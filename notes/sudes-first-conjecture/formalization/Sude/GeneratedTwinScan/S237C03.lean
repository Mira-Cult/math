import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22303)) 497418285 497451053 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497418285 497451053).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22303 497418285 497451053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22304)) 497451053 497483821 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497451053 497483821).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22304 497451053 497483821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22305)) 497483821 497516589 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497483821 497516589).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22305 497483821 497516589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22305)) 497516589 497549357 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497516589 497549357).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22305 497516589 497549357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497418285 497483821).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 497418285 ≤ 497451053)
    (by decide : 497451053 ≤ 497483821) block0 block1

theorem join_0_1 : (twinPrimeSegment 497483821 497549357).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 497483821 ≤ 497516589)
    (by decide : 497516589 ≤ 497549357) block2 block3

theorem join_1_0 : (twinPrimeSegment 497418285 497549357).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 497418285 ≤ 497483821)
    (by decide : 497483821 ≤ 497549357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497418285 497549357).card = 429 := join_1_0

end S237C03
end Sude.GeneratedTwinScan
