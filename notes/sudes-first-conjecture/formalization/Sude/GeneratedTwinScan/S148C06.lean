import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17640)) 311164973 311197741 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311164973 311197741).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17640 311164973 311197741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17641)) 311197741 311230509 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311197741 311230509).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17641 311197741 311230509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17642)) 311230509 311263277 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 311230509 311263277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17642 311230509 311263277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17643)) 311263277 311296045 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311263277 311296045).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17643 311263277 311296045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311164973 311230509).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 311164973 ≤ 311197741)
    (by decide : 311197741 ≤ 311230509) block0 block1

theorem join_0_1 : (twinPrimeSegment 311230509 311296045).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 311230509 ≤ 311263277)
    (by decide : 311263277 ≤ 311296045) block2 block3

theorem join_1_0 : (twinPrimeSegment 311164973 311296045).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 311164973 ≤ 311230509)
    (by decide : 311230509 ≤ 311296045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311164973 311296045).card = 463 := join_1_0

end S148C06
end Sude.GeneratedTwinScan
