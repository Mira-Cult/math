import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19154)) 366870573 366903341 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366870573 366903341).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19154 366870573 366903341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19155)) 366903341 366936109 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366903341 366936109).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19155 366903341 366936109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19156)) 366936109 366968877 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366936109 366968877).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19156 366936109 366968877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19157)) 366968877 367001645 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366968877 367001645).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19157 366968877 367001645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366870573 366936109).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 366870573 ≤ 366903341)
    (by decide : 366903341 ≤ 366936109) block0 block1

theorem join_0_1 : (twinPrimeSegment 366936109 367001645).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 366936109 ≤ 366968877)
    (by decide : 366968877 ≤ 367001645) block2 block3

theorem join_1_0 : (twinPrimeSegment 366870573 367001645).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 366870573 ≤ 366936109)
    (by decide : 366936109 ≤ 367001645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366870573 367001645).card = 431 := join_1_0

end S174C15
end Sude.GeneratedTwinScan
