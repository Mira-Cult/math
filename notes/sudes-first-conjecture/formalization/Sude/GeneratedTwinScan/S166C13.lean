import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18704)) 349831213 349863981 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349831213 349863981).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18704 349831213 349863981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18705)) 349863981 349896749 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349863981 349896749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18705 349863981 349896749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18706)) 349896749 349929517 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 349896749 349929517).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18706 349896749 349929517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18707)) 349929517 349962285 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349929517 349962285).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18707 349929517 349962285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349831213 349896749).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 349831213 ≤ 349863981)
    (by decide : 349863981 ≤ 349896749) block0 block1

theorem join_0_1 : (twinPrimeSegment 349896749 349962285).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 349896749 ≤ 349929517)
    (by decide : 349929517 ≤ 349962285) block2 block3

theorem join_1_0 : (twinPrimeSegment 349831213 349962285).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 349831213 ≤ 349896749)
    (by decide : 349896749 ≤ 349962285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349831213 349962285).card = 432 := join_1_0

end S166C13
end Sude.GeneratedTwinScan
