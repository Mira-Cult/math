import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20823)) 433586221 433618989 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433586221 433618989).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20823 433586221 433618989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20824)) 433618989 433651757 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 433618989 433651757).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20824 433618989 433651757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20825)) 433651757 433684525 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 433651757 433684525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20825 433651757 433684525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20825)) 433684525 433717293 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433684525 433717293).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20825 433684525 433717293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433586221 433651757).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 433586221 ≤ 433618989)
    (by decide : 433618989 ≤ 433651757) block0 block1

theorem join_0_1 : (twinPrimeSegment 433651757 433717293).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 433651757 ≤ 433684525)
    (by decide : 433684525 ≤ 433717293) block2 block3

theorem join_1_0 : (twinPrimeSegment 433586221 433717293).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 433586221 ≤ 433651757)
    (by decide : 433651757 ≤ 433717293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433586221 433717293).card = 449 := join_1_0

end S206C12
end Sude.GeneratedTwinScan
