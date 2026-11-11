import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19684)) 387448877 387481645 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387448877 387481645).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19684 387448877 387481645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19685)) 387481645 387514413 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 387481645 387514413).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19685 387481645 387514413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19686)) 387514413 387547181 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 387514413 387547181).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19686 387514413 387547181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19687)) 387547181 387579949 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387547181 387579949).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19687 387547181 387579949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387448877 387514413).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 387448877 ≤ 387481645)
    (by decide : 387481645 ≤ 387514413) block0 block1

theorem join_0_1 : (twinPrimeSegment 387514413 387579949).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 387514413 ≤ 387547181)
    (by decide : 387547181 ≤ 387579949) block2 block3

theorem join_1_0 : (twinPrimeSegment 387448877 387579949).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 387448877 ≤ 387514413)
    (by decide : 387514413 ≤ 387579949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387448877 387579949).card = 439 := join_1_0

end S184C12
end Sude.GeneratedTwinScan
