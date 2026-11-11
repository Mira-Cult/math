import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16008)) 256245805 256278573 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 256245805 256278573).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16008 256245805 256278573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16009)) 256278573 256311341 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256278573 256311341).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16009 256278573 256311341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16010)) 256311341 256344109 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256311341 256344109).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16010 256311341 256344109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16011)) 256344109 256376877 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256344109 256376877).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16011 256344109 256376877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 256245805 256311341).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 256245805 ≤ 256278573)
    (by decide : 256278573 ≤ 256311341) block0 block1

theorem join_0_1 : (twinPrimeSegment 256311341 256376877).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 256311341 ≤ 256344109)
    (by decide : 256344109 ≤ 256376877) block2 block3

theorem join_1_0 : (twinPrimeSegment 256245805 256376877).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 256245805 ≤ 256311341)
    (by decide : 256311341 ≤ 256376877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 256245805 256376877).card = 447 := join_1_0

end S122C03
end Sude.GeneratedTwinScan
