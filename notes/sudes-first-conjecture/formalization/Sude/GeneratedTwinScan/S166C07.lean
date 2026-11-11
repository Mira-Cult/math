import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18683)) 349044781 349077549 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349044781 349077549).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18683 349044781 349077549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18684)) 349077549 349110317 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349077549 349110317).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18684 349077549 349110317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18685)) 349110317 349143085 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 349110317 349143085).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18685 349110317 349143085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18686)) 349143085 349175853 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349143085 349175853).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18686 349143085 349175853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349044781 349110317).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 349044781 ≤ 349077549)
    (by decide : 349077549 ≤ 349110317) block0 block1

theorem join_0_1 : (twinPrimeSegment 349110317 349175853).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 349110317 ≤ 349143085)
    (by decide : 349143085 ≤ 349175853) block2 block3

theorem join_1_0 : (twinPrimeSegment 349044781 349175853).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 349044781 ≤ 349110317)
    (by decide : 349110317 ≤ 349175853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349044781 349175853).card = 471 := join_1_0

end S166C07
end Sude.GeneratedTwinScan
