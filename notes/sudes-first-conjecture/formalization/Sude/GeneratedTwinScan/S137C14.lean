import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17005)) 289144877 289177645 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289144877 289177645).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17005 289144877 289177645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17006)) 289177645 289210413 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289177645 289210413).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17006 289177645 289210413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17007)) 289210413 289243181 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289210413 289243181).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17007 289210413 289243181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17008)) 289243181 289275949 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 289243181 289275949).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17008 289243181 289275949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289144877 289210413).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 289144877 ≤ 289177645)
    (by decide : 289177645 ≤ 289210413) block0 block1

theorem join_0_1 : (twinPrimeSegment 289210413 289275949).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 289210413 ≤ 289243181)
    (by decide : 289243181 ≤ 289275949) block2 block3

theorem join_1_0 : (twinPrimeSegment 289144877 289275949).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 289144877 ≤ 289210413)
    (by decide : 289210413 ≤ 289275949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289144877 289275949).card = 472 := join_1_0

end S137C14
end Sude.GeneratedTwinScan
