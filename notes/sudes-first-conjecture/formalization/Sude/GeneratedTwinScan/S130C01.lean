import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16516)) 272760877 272793645 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 272760877 272793645).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16516 272760877 272793645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16517)) 272793645 272826413 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272793645 272826413).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16517 272793645 272826413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16518)) 272826413 272859181 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272826413 272859181).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16518 272826413 272859181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16519)) 272859181 272891949 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272859181 272891949).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16519 272859181 272891949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 272760877 272826413).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 272760877 ≤ 272793645)
    (by decide : 272793645 ≤ 272826413) block0 block1

theorem join_0_1 : (twinPrimeSegment 272826413 272891949).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 272826413 ≤ 272859181)
    (by decide : 272859181 ≤ 272891949) block2 block3

theorem join_1_0 : (twinPrimeSegment 272760877 272891949).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 272760877 ≤ 272826413)
    (by decide : 272826413 ≤ 272891949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 272760877 272891949).card = 433 := join_1_0

end S130C01
end Sude.GeneratedTwinScan
