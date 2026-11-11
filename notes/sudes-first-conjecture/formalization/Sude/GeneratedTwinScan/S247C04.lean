import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22771)) 518520877 518553645 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 518520877 518553645).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22771 518520877 518553645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22772)) 518553645 518586413 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 518553645 518586413).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22772 518553645 518586413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22773)) 518586413 518619181 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 518586413 518619181).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22773 518586413 518619181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22773)) 518619181 518651949 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 518619181 518651949).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22773 518619181 518651949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 518520877 518586413).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 518520877 ≤ 518553645)
    (by decide : 518553645 ≤ 518586413) block0 block1

theorem join_0_1 : (twinPrimeSegment 518586413 518651949).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 518586413 ≤ 518619181)
    (by decide : 518619181 ≤ 518651949) block2 block3

theorem join_1_0 : (twinPrimeSegment 518520877 518651949).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 518520877 ≤ 518586413)
    (by decide : 518586413 ≤ 518651949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 518520877 518651949).card = 426 := join_1_0

end S247C04
end Sude.GeneratedTwinScan
