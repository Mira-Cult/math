import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20646)) 426246189 426278957 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 426246189 426278957).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20646 426246189 426278957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20647)) 426278957 426311725 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426278957 426311725).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20647 426278957 426311725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20648)) 426311725 426344493 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 426311725 426344493).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20648 426311725 426344493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20648)) 426344493 426377261 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 426344493 426377261).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20648 426344493 426377261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 426246189 426311725).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 426246189 ≤ 426278957)
    (by decide : 426278957 ≤ 426311725) block0 block1

theorem join_0_1 : (twinPrimeSegment 426311725 426377261).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 426311725 ≤ 426344493)
    (by decide : 426344493 ≤ 426377261) block2 block3

theorem join_1_0 : (twinPrimeSegment 426246189 426377261).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 426246189 ≤ 426311725)
    (by decide : 426311725 ≤ 426377261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 426246189 426377261).card = 449 := join_1_0

end S203C04
end Sude.GeneratedTwinScan
