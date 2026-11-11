import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18113)) 328073261 328106029 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 328073261 328106029).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18113 328073261 328106029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18114)) 328106029 328138797 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 328106029 328138797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18114 328106029 328138797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18115)) 328138797 328171565 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 328138797 328171565).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18115 328138797 328171565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18116)) 328171565 328204333 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 328171565 328204333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18116 328171565 328204333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 328073261 328138797).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 328073261 ≤ 328106029)
    (by decide : 328106029 ≤ 328138797) block0 block1

theorem join_0_1 : (twinPrimeSegment 328138797 328204333).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 328138797 ≤ 328171565)
    (by decide : 328171565 ≤ 328204333) block2 block3

theorem join_1_0 : (twinPrimeSegment 328073261 328204333).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 328073261 ≤ 328138797)
    (by decide : 328138797 ≤ 328204333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 328073261 328204333).card = 435 := join_1_0

end S156C07
end Sude.GeneratedTwinScan
