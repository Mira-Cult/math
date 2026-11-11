import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19837)) 393478189 393510957 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393478189 393510957).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19837 393478189 393510957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19837)) 393510957 393543725 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393510957 393543725).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19837 393510957 393543725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19838)) 393543725 393576493 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393543725 393576493).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19838 393543725 393576493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19839)) 393576493 393609261 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393576493 393609261).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19839 393576493 393609261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393478189 393543725).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 393478189 ≤ 393510957)
    (by decide : 393510957 ≤ 393543725) block0 block1

theorem join_0_1 : (twinPrimeSegment 393543725 393609261).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 393543725 ≤ 393576493)
    (by decide : 393576493 ≤ 393609261) block2 block3

theorem join_1_0 : (twinPrimeSegment 393478189 393609261).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 393478189 ≤ 393543725)
    (by decide : 393543725 ≤ 393609261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393478189 393609261).card = 425 := join_1_0

end S187C10
end Sude.GeneratedTwinScan
