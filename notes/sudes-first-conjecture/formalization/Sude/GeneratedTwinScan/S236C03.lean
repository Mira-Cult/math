import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22256)) 495321133 495353901 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495321133 495353901).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22256 495321133 495353901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22257)) 495353901 495386669 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 495353901 495386669).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22257 495353901 495386669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22258)) 495386669 495419437 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 495386669 495419437).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22258 495386669 495419437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22258)) 495419437 495452205 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495419437 495452205).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22258 495419437 495452205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495321133 495386669).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 495321133 ≤ 495353901)
    (by decide : 495353901 ≤ 495386669) block0 block1

theorem join_0_1 : (twinPrimeSegment 495386669 495452205).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 495386669 ≤ 495419437)
    (by decide : 495419437 ≤ 495452205) block2 block3

theorem join_1_0 : (twinPrimeSegment 495321133 495452205).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 495321133 ≤ 495386669)
    (by decide : 495386669 ≤ 495452205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495321133 495452205).card = 434 := join_1_0

end S236C03
end Sude.GeneratedTwinScan
