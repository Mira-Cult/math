import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22485)) 505544749 505577517 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505544749 505577517).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22485 505544749 505577517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22485)) 505577517 505610285 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505577517 505610285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22485 505577517 505610285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22486)) 505610285 505643053 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505610285 505643053).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22486 505610285 505643053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22487)) 505643053 505675821 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505643053 505675821).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22487 505643053 505675821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505544749 505610285).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 505544749 ≤ 505577517)
    (by decide : 505577517 ≤ 505610285) block0 block1

theorem join_0_1 : (twinPrimeSegment 505610285 505675821).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 505610285 ≤ 505643053)
    (by decide : 505643053 ≤ 505675821) block2 block3

theorem join_1_0 : (twinPrimeSegment 505544749 505675821).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 505544749 ≤ 505610285)
    (by decide : 505610285 ≤ 505675821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505544749 505675821).card = 420 := join_1_0

end S241C01
end Sude.GeneratedTwinScan
