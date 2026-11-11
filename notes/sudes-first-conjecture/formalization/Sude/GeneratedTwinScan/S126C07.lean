import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16284)) 265158701 265191469 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265158701 265191469).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16284 265158701 265191469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16285)) 265191469 265224237 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265191469 265224237).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16285 265191469 265224237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16286)) 265224237 265257005 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 265224237 265257005).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16286 265224237 265257005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16287)) 265257005 265289773 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 265257005 265289773).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16287 265257005 265289773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265158701 265224237).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 265158701 ≤ 265191469)
    (by decide : 265191469 ≤ 265224237) block0 block1

theorem join_0_1 : (twinPrimeSegment 265224237 265289773).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 265224237 ≤ 265257005)
    (by decide : 265257005 ≤ 265289773) block2 block3

theorem join_1_0 : (twinPrimeSegment 265158701 265289773).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 265158701 ≤ 265224237)
    (by decide : 265224237 ≤ 265289773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265158701 265289773).card = 479 := join_1_0

end S126C07
end Sude.GeneratedTwinScan
