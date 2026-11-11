import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17009)) 289275949 289308717 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289275949 289308717).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17009 289275949 289308717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17010)) 289308717 289341485 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289308717 289341485).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17010 289308717 289341485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17011)) 289341485 289374253 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289341485 289374253).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17011 289341485 289374253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17011)) 289374253 289407021 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 289374253 289407021).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17011 289374253 289407021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289275949 289341485).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 289275949 ≤ 289308717)
    (by decide : 289308717 ≤ 289341485) block0 block1

theorem join_0_1 : (twinPrimeSegment 289341485 289407021).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 289341485 ≤ 289374253)
    (by decide : 289374253 ≤ 289407021) block2 block3

theorem join_1_0 : (twinPrimeSegment 289275949 289407021).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 289275949 ≤ 289341485)
    (by decide : 289341485 ≤ 289407021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289275949 289407021).card = 445 := join_1_0

end S137C15
end Sude.GeneratedTwinScan
