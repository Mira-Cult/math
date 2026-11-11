import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19328)) 373555245 373588013 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373555245 373588013).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19328 373555245 373588013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19329)) 373588013 373620781 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373588013 373620781).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19329 373588013 373620781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19330)) 373620781 373653549 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373620781 373653549).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19330 373620781 373653549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19330)) 373653549 373686317 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373653549 373686317).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19330 373653549 373686317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373555245 373620781).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 373555245 ≤ 373588013)
    (by decide : 373588013 ≤ 373620781) block0 block1

theorem join_0_1 : (twinPrimeSegment 373620781 373686317).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 373620781 ≤ 373653549)
    (by decide : 373653549 ≤ 373686317) block2 block3

theorem join_1_0 : (twinPrimeSegment 373555245 373686317).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 373555245 ≤ 373620781)
    (by decide : 373620781 ≤ 373686317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373555245 373686317).card = 439 := join_1_0

end S178C02
end Sude.GeneratedTwinScan
