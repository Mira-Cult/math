import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12893)) 166199341 166232109 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166199341 166232109).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12893 166199341 166232109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12894)) 166232109 166264877 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166232109 166264877).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12894 166232109 166264877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12895)) 166264877 166297645 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166264877 166297645).card = 145 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12895 166264877 166297645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12896)) 166297645 166330413 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166297645 166330413).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12896 166297645 166330413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166199341 166264877).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 166199341 ≤ 166232109)
    (by decide : 166232109 ≤ 166264877) block0 block1

theorem join_0_1 : (twinPrimeSegment 166264877 166330413).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 166264877 ≤ 166297645)
    (by decide : 166297645 ≤ 166330413) block2 block3

theorem join_1_0 : (twinPrimeSegment 166199341 166330413).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 166199341 ≤ 166264877)
    (by decide : 166264877 ≤ 166330413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166199341 166330413).card = 512 := join_1_0

end S079C04
end Sude.GeneratedTwinScan
