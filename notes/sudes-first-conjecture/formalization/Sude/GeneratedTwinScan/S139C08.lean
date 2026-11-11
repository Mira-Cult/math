import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17105)) 292552749 292585517 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292552749 292585517).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17105 292552749 292585517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17106)) 292585517 292618285 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292585517 292618285).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17106 292585517 292618285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17107)) 292618285 292651053 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292618285 292651053).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17107 292618285 292651053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17108)) 292651053 292683821 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292651053 292683821).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17108 292651053 292683821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292552749 292618285).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 292552749 ≤ 292585517)
    (by decide : 292585517 ≤ 292618285) block0 block1

theorem join_0_1 : (twinPrimeSegment 292618285 292683821).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 292618285 ≤ 292651053)
    (by decide : 292651053 ≤ 292683821) block2 block3

theorem join_1_0 : (twinPrimeSegment 292552749 292683821).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 292552749 ≤ 292618285)
    (by decide : 292618285 ≤ 292683821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292552749 292683821).card = 454 := join_1_0

end S139C08
end Sude.GeneratedTwinScan
