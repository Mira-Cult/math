import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14153)) 200278061 200310829 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 200278061 200310829).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14153 200278061 200310829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14154)) 200310829 200343597 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 200310829 200343597).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14154 200310829 200343597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14155)) 200343597 200376365 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 200343597 200376365).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14155 200343597 200376365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14156)) 200376365 200409133 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 200376365 200409133).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14156 200376365 200409133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 200278061 200343597).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 200278061 ≤ 200310829)
    (by decide : 200310829 ≤ 200343597) block0 block1

theorem join_0_1 : (twinPrimeSegment 200343597 200409133).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 200343597 ≤ 200376365)
    (by decide : 200376365 ≤ 200409133) block2 block3

theorem join_1_0 : (twinPrimeSegment 200278061 200409133).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 200278061 ≤ 200343597)
    (by decide : 200343597 ≤ 200409133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 200278061 200409133).card = 452 := join_1_0

end S095C08
end Sude.GeneratedTwinScan
