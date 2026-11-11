import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17836)) 318111789 318144557 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318111789 318144557).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17836 318111789 318144557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17837)) 318144557 318177325 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318144557 318177325).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17837 318144557 318177325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17838)) 318177325 318210093 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318177325 318210093).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17838 318177325 318210093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17839)) 318210093 318242861 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318210093 318242861).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17839 318210093 318242861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318111789 318177325).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 318111789 ≤ 318144557)
    (by decide : 318144557 ≤ 318177325) block0 block1

theorem join_0_1 : (twinPrimeSegment 318177325 318242861).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 318177325 ≤ 318210093)
    (by decide : 318210093 ≤ 318242861) block2 block3

theorem join_1_0 : (twinPrimeSegment 318111789 318242861).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 318111789 ≤ 318177325)
    (by decide : 318177325 ≤ 318242861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318111789 318242861).card = 469 := join_1_0

end S151C11
end Sude.GeneratedTwinScan
