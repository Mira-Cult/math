import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17363)) 301465645 301498413 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301465645 301498413).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17363 301465645 301498413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17364)) 301498413 301531181 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 301498413 301531181).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17364 301498413 301531181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17365)) 301531181 301563949 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301531181 301563949).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17365 301531181 301563949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17366)) 301563949 301596717 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301563949 301596717).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17366 301563949 301596717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301465645 301531181).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 301465645 ≤ 301498413)
    (by decide : 301498413 ≤ 301531181) block0 block1

theorem join_0_1 : (twinPrimeSegment 301531181 301596717).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 301531181 ≤ 301563949)
    (by decide : 301563949 ≤ 301596717) block2 block3

theorem join_1_0 : (twinPrimeSegment 301465645 301596717).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 301465645 ≤ 301531181)
    (by decide : 301531181 ≤ 301596717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301465645 301596717).card = 442 := join_1_0

end S143C12
end Sude.GeneratedTwinScan
