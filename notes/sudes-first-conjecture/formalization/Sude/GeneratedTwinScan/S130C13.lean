import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16564)) 274333741 274366509 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274333741 274366509).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16564 274333741 274366509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16565)) 274366509 274399277 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274366509 274399277).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16565 274366509 274399277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16565)) 274399277 274432045 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274399277 274432045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16565 274399277 274432045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16566)) 274432045 274464813 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274432045 274464813).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16566 274432045 274464813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274333741 274399277).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 274333741 ≤ 274366509)
    (by decide : 274366509 ≤ 274399277) block0 block1

theorem join_0_1 : (twinPrimeSegment 274399277 274464813).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 274399277 ≤ 274432045)
    (by decide : 274432045 ≤ 274464813) block2 block3

theorem join_1_0 : (twinPrimeSegment 274333741 274464813).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 274333741 ≤ 274399277)
    (by decide : 274399277 ≤ 274464813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274333741 274464813).card = 459 := join_1_0

end S130C13
end Sude.GeneratedTwinScan
