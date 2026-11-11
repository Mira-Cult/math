import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21686)) 470286381 470319149 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 470286381 470319149).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21686 470286381 470319149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21687)) 470319149 470351917 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 470319149 470351917).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21687 470319149 470351917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21688)) 470351917 470384685 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 470351917 470384685).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21688 470351917 470384685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21689)) 470384685 470417453 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 470384685 470417453).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21689 470384685 470417453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 470286381 470351917).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 470286381 ≤ 470319149)
    (by decide : 470319149 ≤ 470351917) block0 block1

theorem join_0_1 : (twinPrimeSegment 470351917 470417453).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 470351917 ≤ 470384685)
    (by decide : 470384685 ≤ 470417453) block2 block3

theorem join_1_0 : (twinPrimeSegment 470286381 470417453).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 470286381 ≤ 470351917)
    (by decide : 470351917 ≤ 470417453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 470286381 470417453).card = 432 := join_1_0

end S224C04
end Sude.GeneratedTwinScan
