import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22543)) 508166189 508198957 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508166189 508198957).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22543 508166189 508198957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22543)) 508198957 508231725 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508198957 508231725).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22543 508198957 508231725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22544)) 508231725 508264493 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 508231725 508264493).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22544 508231725 508264493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22545)) 508264493 508297261 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508264493 508297261).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22545 508264493 508297261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508166189 508231725).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 508166189 ≤ 508198957)
    (by decide : 508198957 ≤ 508231725) block0 block1

theorem join_0_1 : (twinPrimeSegment 508231725 508297261).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 508231725 ≤ 508264493)
    (by decide : 508264493 ≤ 508297261) block2 block3

theorem join_1_0 : (twinPrimeSegment 508166189 508297261).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 508166189 ≤ 508231725)
    (by decide : 508231725 ≤ 508297261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508166189 508297261).card = 447 := join_1_0

end S242C05
end Sude.GeneratedTwinScan
