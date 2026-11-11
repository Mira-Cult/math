import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20792)) 432275501 432308269 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 432275501 432308269).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20792 432275501 432308269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20792)) 432308269 432341037 = 78 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 432308269 432341037).card = 78 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20792 432308269 432341037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20793)) 432341037 432373805 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 432341037 432373805).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20793 432341037 432373805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20794)) 432373805 432406573 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 432373805 432406573).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20794 432373805 432406573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 432275501 432341037).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 432275501 ≤ 432308269)
    (by decide : 432308269 ≤ 432341037) block0 block1

theorem join_0_1 : (twinPrimeSegment 432341037 432406573).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 432341037 ≤ 432373805)
    (by decide : 432373805 ≤ 432406573) block2 block3

theorem join_1_0 : (twinPrimeSegment 432275501 432406573).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 432275501 ≤ 432341037)
    (by decide : 432341037 ≤ 432406573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 432275501 432406573).card = 420 := join_1_0

end S206C02
end Sude.GeneratedTwinScan
