import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20432)) 417464365 417497133 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417464365 417497133).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20432 417464365 417497133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20433)) 417497133 417529901 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417497133 417529901).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20433 417497133 417529901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20434)) 417529901 417562669 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417529901 417562669).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20434 417529901 417562669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20435)) 417562669 417595437 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417562669 417595437).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20435 417562669 417595437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417464365 417529901).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 417464365 ≤ 417497133)
    (by decide : 417497133 ≤ 417529901) block0 block1

theorem join_0_1 : (twinPrimeSegment 417529901 417595437).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 417529901 ≤ 417562669)
    (by decide : 417562669 ≤ 417595437) block2 block3

theorem join_1_0 : (twinPrimeSegment 417464365 417595437).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 417464365 ≤ 417529901)
    (by decide : 417529901 ≤ 417595437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417464365 417595437).card = 456 := join_1_0

end S199C01
end Sude.GeneratedTwinScan
