import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22227)) 494010413 494043181 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494010413 494043181).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22227 494010413 494043181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22227)) 494043181 494075949 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494043181 494075949).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22227 494043181 494075949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22228)) 494075949 494108717 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494075949 494108717).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22228 494075949 494108717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22229)) 494108717 494141485 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494108717 494141485).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22229 494108717 494141485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494010413 494075949).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 494010413 ≤ 494043181)
    (by decide : 494043181 ≤ 494075949) block0 block1

theorem join_0_1 : (twinPrimeSegment 494075949 494141485).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 494075949 ≤ 494108717)
    (by decide : 494108717 ≤ 494141485) block2 block3

theorem join_1_0 : (twinPrimeSegment 494010413 494141485).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 494010413 ≤ 494075949)
    (by decide : 494075949 ≤ 494141485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494010413 494141485).card = 415 := join_1_0

end S235C09
end Sude.GeneratedTwinScan
