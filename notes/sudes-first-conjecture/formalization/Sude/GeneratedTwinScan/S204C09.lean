import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20713)) 428998701 429031469 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428998701 429031469).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20713 428998701 429031469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20713)) 429031469 429064237 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429031469 429064237).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20713 429031469 429064237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20714)) 429064237 429097005 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429064237 429097005).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20714 429064237 429097005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20715)) 429097005 429129773 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 429097005 429129773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20715 429097005 429129773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428998701 429064237).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 428998701 ≤ 429031469)
    (by decide : 429031469 ≤ 429064237) block0 block1

theorem join_0_1 : (twinPrimeSegment 429064237 429129773).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 429064237 ≤ 429097005)
    (by decide : 429097005 ≤ 429129773) block2 block3

theorem join_1_0 : (twinPrimeSegment 428998701 429129773).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 428998701 ≤ 429064237)
    (by decide : 429064237 ≤ 429129773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428998701 429129773).card = 443 := join_1_0

end S204C09
end Sude.GeneratedTwinScan
