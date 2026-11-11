import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22076)) 487325741 487358509 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487325741 487358509).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22076 487325741 487358509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22076)) 487358509 487391277 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487358509 487391277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22076 487358509 487391277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22077)) 487391277 487424045 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487391277 487424045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22077 487391277 487424045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22078)) 487424045 487456813 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487424045 487456813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22078 487424045 487456813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487325741 487391277).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 487325741 ≤ 487358509)
    (by decide : 487358509 ≤ 487391277) block0 block1

theorem join_0_1 : (twinPrimeSegment 487391277 487456813).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 487391277 ≤ 487424045)
    (by decide : 487424045 ≤ 487456813) block2 block3

theorem join_1_0 : (twinPrimeSegment 487325741 487456813).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 487325741 ≤ 487391277)
    (by decide : 487391277 ≤ 487456813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487325741 487456813).card = 447 := join_1_0

end S232C06
end Sude.GeneratedTwinScan
