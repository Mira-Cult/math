import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21351)) 455868461 455901229 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 455868461 455901229).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21351 455868461 455901229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21352)) 455901229 455933997 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 455901229 455933997).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21352 455901229 455933997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21353)) 455933997 455966765 = 88 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 455933997 455966765).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21353 455933997 455966765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21354)) 455966765 455999533 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 455966765 455999533).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21354 455966765 455999533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 455868461 455933997).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 455868461 ≤ 455901229)
    (by decide : 455901229 ≤ 455933997) block0 block1

theorem join_0_1 : (twinPrimeSegment 455933997 455999533).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 455933997 ≤ 455966765)
    (by decide : 455966765 ≤ 455999533) block2 block3

theorem join_1_0 : (twinPrimeSegment 455868461 455999533).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 455868461 ≤ 455933997)
    (by decide : 455933997 ≤ 455999533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 455868461 455999533).card = 417 := join_1_0

end S217C06
end Sude.GeneratedTwinScan
