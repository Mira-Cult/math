import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17755)) 315228205 315260973 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 315228205 315260973).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17755 315228205 315260973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17756)) 315260973 315293741 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 315260973 315293741).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17756 315260973 315293741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17757)) 315293741 315326509 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 315293741 315326509).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17757 315293741 315326509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17758)) 315326509 315359277 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 315326509 315359277).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17758 315326509 315359277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 315228205 315293741).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 315228205 ≤ 315260973)
    (by decide : 315260973 ≤ 315293741) block0 block1

theorem join_0_1 : (twinPrimeSegment 315293741 315359277).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 315293741 ≤ 315326509)
    (by decide : 315326509 ≤ 315359277) block2 block3

theorem join_1_0 : (twinPrimeSegment 315228205 315359277).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 315228205 ≤ 315293741)
    (by decide : 315293741 ≤ 315359277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 315228205 315359277).card = 450 := join_1_0

end S150C05
end Sude.GeneratedTwinScan
