import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16224)) 263192621 263225389 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263192621 263225389).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16224 263192621 263225389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16225)) 263225389 263258157 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263225389 263258157).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16225 263225389 263258157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16226)) 263258157 263290925 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263258157 263290925).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16226 263258157 263290925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16227)) 263290925 263323693 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263290925 263323693).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16227 263290925 263323693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263192621 263258157).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 263192621 ≤ 263225389)
    (by decide : 263225389 ≤ 263258157) block0 block1

theorem join_0_1 : (twinPrimeSegment 263258157 263323693).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 263258157 ≤ 263290925)
    (by decide : 263290925 ≤ 263323693) block2 block3

theorem join_1_0 : (twinPrimeSegment 263192621 263323693).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 263192621 ≤ 263258157)
    (by decide : 263258157 ≤ 263323693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263192621 263323693).card = 481 := join_1_0

end S125C08
end Sude.GeneratedTwinScan
