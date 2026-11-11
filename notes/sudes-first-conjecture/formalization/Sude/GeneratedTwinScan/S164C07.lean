import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18571)) 344850477 344883245 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344850477 344883245).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18571 344850477 344883245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18571)) 344883245 344916013 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344883245 344916013).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18571 344883245 344916013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18572)) 344916013 344948781 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344916013 344948781).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18572 344916013 344948781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18573)) 344948781 344981549 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344948781 344981549).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18573 344948781 344981549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344850477 344916013).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 344850477 ≤ 344883245)
    (by decide : 344883245 ≤ 344916013) block0 block1

theorem join_0_1 : (twinPrimeSegment 344916013 344981549).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 344916013 ≤ 344948781)
    (by decide : 344948781 ≤ 344981549) block2 block3

theorem join_1_0 : (twinPrimeSegment 344850477 344981549).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 344850477 ≤ 344916013)
    (by decide : 344916013 ≤ 344981549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344850477 344981549).card = 445 := join_1_0

end S164C07
end Sude.GeneratedTwinScan
