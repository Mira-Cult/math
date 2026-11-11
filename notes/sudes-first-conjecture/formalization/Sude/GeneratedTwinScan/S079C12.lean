import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12933)) 167247917 167280685 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167247917 167280685).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12933 167247917 167280685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12934)) 167280685 167313453 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167280685 167313453).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12934 167280685 167313453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12936)) 167313453 167346221 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167313453 167346221).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12936 167313453 167346221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12937)) 167346221 167378989 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167346221 167378989).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12937 167346221 167378989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167247917 167313453).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 167247917 ≤ 167280685)
    (by decide : 167280685 ≤ 167313453) block0 block1

theorem join_0_1 : (twinPrimeSegment 167313453 167378989).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 167313453 ≤ 167346221)
    (by decide : 167346221 ≤ 167378989) block2 block3

theorem join_1_0 : (twinPrimeSegment 167247917 167378989).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 167247917 ≤ 167313453)
    (by decide : 167313453 ≤ 167378989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167247917 167378989).card = 450 := join_1_0

end S079C12
end Sude.GeneratedTwinScan
