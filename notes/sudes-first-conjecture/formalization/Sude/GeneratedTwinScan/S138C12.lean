import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17059)) 290979885 291012653 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290979885 291012653).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17059 290979885 291012653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17060)) 291012653 291045421 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291012653 291045421).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17060 291012653 291045421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17061)) 291045421 291078189 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291045421 291078189).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17061 291045421 291078189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17061)) 291078189 291110957 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291078189 291110957).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17061 291078189 291110957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290979885 291045421).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 290979885 ≤ 291012653)
    (by decide : 291012653 ≤ 291045421) block0 block1

theorem join_0_1 : (twinPrimeSegment 291045421 291110957).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 291045421 ≤ 291078189)
    (by decide : 291078189 ≤ 291110957) block2 block3

theorem join_1_0 : (twinPrimeSegment 290979885 291110957).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 290979885 ≤ 291045421)
    (by decide : 291045421 ≤ 291110957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290979885 291110957).card = 427 := join_1_0

end S138C12
end Sude.GeneratedTwinScan
