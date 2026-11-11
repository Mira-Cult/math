import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13377)) 178913325 178946093 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 178913325 178946093).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13377 178913325 178946093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13378)) 178946093 178978861 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178946093 178978861).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13378 178946093 178978861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13379)) 178978861 179011629 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178978861 179011629).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13379 178978861 179011629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13380)) 179011629 179044397 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179011629 179044397).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13380 179011629 179044397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 178913325 178978861).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 178913325 ≤ 178946093)
    (by decide : 178946093 ≤ 178978861) block0 block1

theorem join_0_1 : (twinPrimeSegment 178978861 179044397).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 178978861 ≤ 179011629)
    (by decide : 179011629 ≤ 179044397) block2 block3

theorem join_1_0 : (twinPrimeSegment 178913325 179044397).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 178913325 ≤ 178978861)
    (by decide : 178978861 ≤ 179044397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 178913325 179044397).card = 497 := join_1_0

end S085C05
end Sude.GeneratedTwinScan
