import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21271)) 452460589 452493357 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452460589 452493357).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21271 452460589 452493357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21272)) 452493357 452526125 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452493357 452526125).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21272 452493357 452526125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21273)) 452526125 452558893 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452526125 452558893).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21273 452526125 452558893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21274)) 452558893 452591661 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452558893 452591661).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21274 452558893 452591661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452460589 452526125).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 452460589 ≤ 452493357)
    (by decide : 452493357 ≤ 452526125) block0 block1

theorem join_0_1 : (twinPrimeSegment 452526125 452591661).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 452526125 ≤ 452558893)
    (by decide : 452558893 ≤ 452591661) block2 block3

theorem join_1_0 : (twinPrimeSegment 452460589 452591661).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 452460589 ≤ 452526125)
    (by decide : 452526125 ≤ 452591661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452460589 452591661).card = 416 := join_1_0

end S215C12
end Sude.GeneratedTwinScan
