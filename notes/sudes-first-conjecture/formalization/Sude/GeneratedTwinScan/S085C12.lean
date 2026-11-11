import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13411)) 179830829 179863597 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179830829 179863597).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13411 179830829 179863597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13412)) 179863597 179896365 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179863597 179896365).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13412 179863597 179896365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13413)) 179896365 179929133 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 179896365 179929133).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13413 179896365 179929133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13414)) 179929133 179961901 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179929133 179961901).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13414 179929133 179961901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179830829 179896365).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 179830829 ≤ 179863597)
    (by decide : 179863597 ≤ 179896365) block0 block1

theorem join_0_1 : (twinPrimeSegment 179896365 179961901).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 179896365 ≤ 179929133)
    (by decide : 179929133 ≤ 179961901) block2 block3

theorem join_1_0 : (twinPrimeSegment 179830829 179961901).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 179830829 ≤ 179896365)
    (by decide : 179896365 ≤ 179961901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179830829 179961901).card = 450 := join_1_0

end S085C12
end Sude.GeneratedTwinScan
