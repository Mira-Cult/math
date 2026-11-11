import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21843)) 477102125 477134893 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 477102125 477134893).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21843 477102125 477134893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21844)) 477134893 477167661 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477134893 477167661).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21844 477134893 477167661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21844)) 477167661 477200429 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477167661 477200429).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21844 477167661 477200429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21845)) 477200429 477233197 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477200429 477233197).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21845 477200429 477233197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 477102125 477167661).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 477102125 ≤ 477134893)
    (by decide : 477134893 ≤ 477167661) block0 block1

theorem join_0_1 : (twinPrimeSegment 477167661 477233197).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 477167661 ≤ 477200429)
    (by decide : 477200429 ≤ 477233197) block2 block3

theorem join_1_0 : (twinPrimeSegment 477102125 477233197).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 477102125 ≤ 477167661)
    (by decide : 477167661 ≤ 477233197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 477102125 477233197).card = 427 := join_1_0

end S227C08
end Sude.GeneratedTwinScan
