import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22105)) 488636461 488669229 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 488636461 488669229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22105 488636461 488669229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22106)) 488669229 488701997 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488669229 488701997).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22106 488669229 488701997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22107)) 488701997 488734765 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488701997 488734765).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22107 488701997 488734765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22108)) 488734765 488767533 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488734765 488767533).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22108 488734765 488767533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 488636461 488701997).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 488636461 ≤ 488669229)
    (by decide : 488669229 ≤ 488701997) block0 block1

theorem join_0_1 : (twinPrimeSegment 488701997 488767533).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 488701997 ≤ 488734765)
    (by decide : 488734765 ≤ 488767533) block2 block3

theorem join_1_0 : (twinPrimeSegment 488636461 488767533).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 488636461 ≤ 488701997)
    (by decide : 488701997 ≤ 488767533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 488636461 488767533).card = 426 := join_1_0

end S233C00
end Sude.GeneratedTwinScan
