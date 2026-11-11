import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21701)) 470941741 470974509 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 470941741 470974509).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21701 470941741 470974509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21702)) 470974509 471007277 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 470974509 471007277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21702 470974509 471007277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21703)) 471007277 471040045 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471007277 471040045).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21703 471007277 471040045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21704)) 471040045 471072813 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471040045 471072813).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21704 471040045 471072813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 470941741 471007277).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 470941741 ≤ 470974509)
    (by decide : 470974509 ≤ 471007277) block0 block1

theorem join_0_1 : (twinPrimeSegment 471007277 471072813).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 471007277 ≤ 471040045)
    (by decide : 471040045 ≤ 471072813) block2 block3

theorem join_1_0 : (twinPrimeSegment 470941741 471072813).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 470941741 ≤ 471007277)
    (by decide : 471007277 ≤ 471072813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 470941741 471072813).card = 450 := join_1_0

end S224C09
end Sude.GeneratedTwinScan
