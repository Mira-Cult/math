import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17480)) 305528877 305561645 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305528877 305561645).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17480 305528877 305561645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17481)) 305561645 305594413 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305561645 305594413).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17481 305561645 305594413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17482)) 305594413 305627181 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305594413 305627181).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17482 305594413 305627181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17483)) 305627181 305659949 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305627181 305659949).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17483 305627181 305659949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305528877 305594413).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 305528877 ≤ 305561645)
    (by decide : 305561645 ≤ 305594413) block0 block1

theorem join_0_1 : (twinPrimeSegment 305594413 305659949).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 305594413 ≤ 305627181)
    (by decide : 305627181 ≤ 305659949) block2 block3

theorem join_1_0 : (twinPrimeSegment 305528877 305659949).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 305528877 ≤ 305594413)
    (by decide : 305594413 ≤ 305659949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305528877 305659949).card = 460 := join_1_0

end S145C11
end Sude.GeneratedTwinScan
