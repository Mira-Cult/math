import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14608)) 213385261 213418029 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 213385261 213418029).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14608 213385261 213418029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14609)) 213418029 213450797 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213418029 213450797).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14609 213418029 213450797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14611)) 213450797 213483565 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213450797 213483565).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14611 213450797 213483565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14612)) 213483565 213516333 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 213483565 213516333).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14612 213483565 213516333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 213385261 213450797).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 213385261 ≤ 213418029)
    (by decide : 213418029 ≤ 213450797) block0 block1

theorem join_0_1 : (twinPrimeSegment 213450797 213516333).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 213450797 ≤ 213483565)
    (by decide : 213483565 ≤ 213516333) block2 block3

theorem join_1_0 : (twinPrimeSegment 213385261 213516333).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 213385261 ≤ 213450797)
    (by decide : 213450797 ≤ 213516333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 213385261 213516333).card = 475 := join_1_0

end S101C12
end Sude.GeneratedTwinScan
