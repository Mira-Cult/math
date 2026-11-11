import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19681)) 387317805 387350573 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387317805 387350573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19681 387317805 387350573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19682)) 387350573 387383341 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 387350573 387383341).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19682 387350573 387383341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19682)) 387383341 387416109 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 387383341 387416109).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19682 387383341 387416109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19683)) 387416109 387448877 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387416109 387448877).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19683 387416109 387448877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387317805 387383341).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 387317805 ≤ 387350573)
    (by decide : 387350573 ≤ 387383341) block0 block1

theorem join_0_1 : (twinPrimeSegment 387383341 387448877).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 387383341 ≤ 387416109)
    (by decide : 387416109 ≤ 387448877) block2 block3

theorem join_1_0 : (twinPrimeSegment 387317805 387448877).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 387317805 ≤ 387383341)
    (by decide : 387383341 ≤ 387448877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387317805 387448877).card = 466 := join_1_0

end S184C11
end Sude.GeneratedTwinScan
