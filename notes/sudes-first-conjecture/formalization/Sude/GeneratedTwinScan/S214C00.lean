import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21185)) 448790573 448823341 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448790573 448823341).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21185 448790573 448823341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21186)) 448823341 448856109 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448823341 448856109).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21186 448823341 448856109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21186)) 448856109 448888877 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448856109 448888877).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21186 448856109 448888877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21187)) 448888877 448921645 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448888877 448921645).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21187 448888877 448921645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448790573 448856109).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 448823341)
    (by decide : 448823341 ≤ 448856109) block0 block1

theorem join_0_1 : (twinPrimeSegment 448856109 448921645).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 448856109 ≤ 448888877)
    (by decide : 448888877 ≤ 448921645) block2 block3

theorem join_1_0 : (twinPrimeSegment 448790573 448921645).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 448856109)
    (by decide : 448856109 ≤ 448921645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448790573 448921645).card = 453 := join_1_0

end S214C00
end Sude.GeneratedTwinScan
