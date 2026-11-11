import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14675)) 215351341 215384109 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 215351341 215384109).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14675 215351341 215384109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14677)) 215384109 215416877 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 215384109 215416877).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14677 215384109 215416877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14678)) 215416877 215449645 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215416877 215449645).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14678 215416877 215449645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14679)) 215449645 215482413 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215449645 215482413).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14679 215449645 215482413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 215351341 215416877).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 215351341 ≤ 215384109)
    (by decide : 215384109 ≤ 215416877) block0 block1

theorem join_0_1 : (twinPrimeSegment 215416877 215482413).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 215416877 ≤ 215449645)
    (by decide : 215449645 ≤ 215482413) block2 block3

theorem join_1_0 : (twinPrimeSegment 215351341 215482413).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 215351341 ≤ 215416877)
    (by decide : 215416877 ≤ 215482413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 215351341 215482413).card = 453 := join_1_0

end S102C11
end Sude.GeneratedTwinScan
