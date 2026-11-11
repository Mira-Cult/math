import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22224)) 493879341 493912109 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493879341 493912109).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22224 493879341 493912109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22224)) 493912109 493944877 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493912109 493944877).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22224 493912109 493944877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22225)) 493944877 493977645 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493944877 493977645).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22225 493944877 493977645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22226)) 493977645 494010413 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493977645 494010413).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22226 493977645 494010413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493879341 493944877).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 493879341 ≤ 493912109)
    (by decide : 493912109 ≤ 493944877) block0 block1

theorem join_0_1 : (twinPrimeSegment 493944877 494010413).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 493944877 ≤ 493977645)
    (by decide : 493977645 ≤ 494010413) block2 block3

theorem join_1_0 : (twinPrimeSegment 493879341 494010413).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 493879341 ≤ 493944877)
    (by decide : 493944877 ≤ 494010413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493879341 494010413).card = 453 := join_1_0

end S235C08
end Sude.GeneratedTwinScan
