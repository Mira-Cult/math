import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19439)) 377880621 377913389 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377880621 377913389).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19439 377880621 377913389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19440)) 377913389 377946157 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377913389 377946157).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19440 377913389 377946157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19441)) 377946157 377978925 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377946157 377978925).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19441 377946157 377978925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19442)) 377978925 378011693 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377978925 378011693).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19442 377978925 378011693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377880621 377946157).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 377880621 ≤ 377913389)
    (by decide : 377913389 ≤ 377946157) block0 block1

theorem join_0_1 : (twinPrimeSegment 377946157 378011693).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 377946157 ≤ 377978925)
    (by decide : 377978925 ≤ 378011693) block2 block3

theorem join_1_0 : (twinPrimeSegment 377880621 378011693).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 377880621 ≤ 377946157)
    (by decide : 377946157 ≤ 378011693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377880621 378011693).card = 478 := join_1_0

end S180C03
end Sude.GeneratedTwinScan
