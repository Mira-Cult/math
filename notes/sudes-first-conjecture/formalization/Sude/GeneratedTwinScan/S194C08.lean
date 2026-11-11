import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20197)) 407896109 407928877 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 407896109 407928877).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20197 407896109 407928877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20198)) 407928877 407961645 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407928877 407961645).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20198 407928877 407961645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20198)) 407961645 407994413 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407961645 407994413).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20198 407961645 407994413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20199)) 407994413 408027181 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407994413 408027181).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20199 407994413 408027181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 407896109 407961645).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 407896109 ≤ 407928877)
    (by decide : 407928877 ≤ 407961645) block0 block1

theorem join_0_1 : (twinPrimeSegment 407961645 408027181).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 407961645 ≤ 407994413)
    (by decide : 407994413 ≤ 408027181) block2 block3

theorem join_1_0 : (twinPrimeSegment 407896109 408027181).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 407896109 ≤ 407961645)
    (by decide : 407961645 ≤ 408027181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 407896109 408027181).card = 464 := join_1_0

end S194C08
end Sude.GeneratedTwinScan
