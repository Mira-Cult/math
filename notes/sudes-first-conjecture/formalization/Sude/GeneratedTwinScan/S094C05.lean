import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14064)) 197787693 197820461 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197787693 197820461).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14064 197787693 197820461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14066)) 197820461 197853229 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197820461 197853229).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14066 197820461 197853229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14067)) 197853229 197885997 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197853229 197885997).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14067 197853229 197885997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14068)) 197885997 197918765 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197885997 197918765).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14068 197885997 197918765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197787693 197853229).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 197787693 ≤ 197820461)
    (by decide : 197820461 ≤ 197853229) block0 block1

theorem join_0_1 : (twinPrimeSegment 197853229 197918765).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 197853229 ≤ 197885997)
    (by decide : 197885997 ≤ 197918765) block2 block3

theorem join_1_0 : (twinPrimeSegment 197787693 197918765).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 197787693 ≤ 197853229)
    (by decide : 197853229 ≤ 197918765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197787693 197918765).card = 478 := join_1_0

end S094C05
end Sude.GeneratedTwinScan
