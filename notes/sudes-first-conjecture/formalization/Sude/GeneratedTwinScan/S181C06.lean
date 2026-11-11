import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19503)) 380370989 380403757 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 380370989 380403757).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19503 380370989 380403757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19504)) 380403757 380436525 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380403757 380436525).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19504 380403757 380436525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19505)) 380436525 380469293 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380436525 380469293).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19505 380436525 380469293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19506)) 380469293 380502061 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380469293 380502061).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19506 380469293 380502061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 380370989 380436525).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 380370989 ≤ 380403757)
    (by decide : 380403757 ≤ 380436525) block0 block1

theorem join_0_1 : (twinPrimeSegment 380436525 380502061).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 380436525 ≤ 380469293)
    (by decide : 380469293 ≤ 380502061) block2 block3

theorem join_1_0 : (twinPrimeSegment 380370989 380502061).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 380370989 ≤ 380436525)
    (by decide : 380436525 ≤ 380502061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 380370989 380502061).card = 484 := join_1_0

end S181C06
end Sude.GeneratedTwinScan
