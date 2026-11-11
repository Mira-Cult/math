import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15037)) 226099245 226132013 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 226099245 226132013).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15037 226099245 226132013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15038)) 226132013 226164781 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 226132013 226164781).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15038 226132013 226164781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15039)) 226164781 226197549 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 226164781 226197549).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15039 226164781 226197549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15040)) 226197549 226230317 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 226197549 226230317).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15040 226197549 226230317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 226099245 226164781).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 226099245 ≤ 226132013)
    (by decide : 226132013 ≤ 226164781) block0 block1

theorem join_0_1 : (twinPrimeSegment 226164781 226230317).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 226164781 ≤ 226197549)
    (by decide : 226197549 ≤ 226230317) block2 block3

theorem join_1_0 : (twinPrimeSegment 226099245 226230317).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 226099245 ≤ 226164781)
    (by decide : 226164781 ≤ 226230317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 226099245 226230317).card = 495 := join_1_0

end S107C13
end Sude.GeneratedTwinScan
