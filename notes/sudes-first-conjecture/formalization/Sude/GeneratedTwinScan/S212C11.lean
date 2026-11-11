import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21120)) 446038061 446070829 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446038061 446070829).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21120 446038061 446070829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21121)) 446070829 446103597 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446070829 446103597).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21121 446070829 446103597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21121)) 446103597 446136365 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446103597 446136365).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21121 446103597 446136365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21122)) 446136365 446169133 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446136365 446169133).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21122 446136365 446169133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446038061 446103597).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 446038061 ≤ 446070829)
    (by decide : 446070829 ≤ 446103597) block0 block1

theorem join_0_1 : (twinPrimeSegment 446103597 446169133).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 446103597 ≤ 446136365)
    (by decide : 446136365 ≤ 446169133) block2 block3

theorem join_1_0 : (twinPrimeSegment 446038061 446169133).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 446038061 ≤ 446103597)
    (by decide : 446103597 ≤ 446169133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446038061 446169133).card = 462 := join_1_0

end S212C11
end Sude.GeneratedTwinScan
