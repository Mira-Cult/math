import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12672)) 160563245 160596013 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160563245 160596013).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12672 160563245 160596013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12673)) 160596013 160628781 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160596013 160628781).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12673 160596013 160628781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12675)) 160628781 160661549 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160628781 160661549).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12675 160628781 160661549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12676)) 160661549 160694317 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160661549 160694317).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12676 160661549 160694317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160563245 160628781).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 160563245 ≤ 160596013)
    (by decide : 160596013 ≤ 160628781) block0 block1

theorem join_0_1 : (twinPrimeSegment 160628781 160694317).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 160628781 ≤ 160661549)
    (by decide : 160661549 ≤ 160694317) block2 block3

theorem join_1_0 : (twinPrimeSegment 160563245 160694317).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 160563245 ≤ 160628781)
    (by decide : 160628781 ≤ 160694317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160563245 160694317).card = 471 := join_1_0

end S076C09
end Sude.GeneratedTwinScan
