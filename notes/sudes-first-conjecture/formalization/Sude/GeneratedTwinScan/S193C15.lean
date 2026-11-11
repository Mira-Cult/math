import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20168)) 406716461 406749229 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406716461 406749229).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20168 406716461 406749229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20168)) 406749229 406781997 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406749229 406781997).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20168 406749229 406781997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20169)) 406781997 406814765 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406781997 406814765).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20169 406781997 406814765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20170)) 406814765 406847533 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406814765 406847533).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20170 406814765 406847533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406716461 406781997).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 406716461 ≤ 406749229)
    (by decide : 406749229 ≤ 406781997) block0 block1

theorem join_0_1 : (twinPrimeSegment 406781997 406847533).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 406781997 ≤ 406814765)
    (by decide : 406814765 ≤ 406847533) block2 block3

theorem join_1_0 : (twinPrimeSegment 406716461 406847533).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 406716461 ≤ 406781997)
    (by decide : 406781997 ≤ 406847533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406716461 406847533).card = 466 := join_1_0

end S193C15
end Sude.GeneratedTwinScan
