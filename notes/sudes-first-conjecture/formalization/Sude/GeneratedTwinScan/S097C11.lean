import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14314)) 204865581 204898349 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204865581 204898349).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14314 204865581 204898349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14315)) 204898349 204931117 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204898349 204931117).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14315 204898349 204931117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14316)) 204931117 204963885 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204931117 204963885).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14316 204931117 204963885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14317)) 204963885 204996653 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204963885 204996653).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14317 204963885 204996653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204865581 204931117).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 204865581 ≤ 204898349)
    (by decide : 204898349 ≤ 204931117) block0 block1

theorem join_0_1 : (twinPrimeSegment 204931117 204996653).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 204931117 ≤ 204963885)
    (by decide : 204963885 ≤ 204996653) block2 block3

theorem join_1_0 : (twinPrimeSegment 204865581 204996653).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 204865581 ≤ 204931117)
    (by decide : 204931117 ≤ 204996653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204865581 204996653).card = 500 := join_1_0

end S097C11
end Sude.GeneratedTwinScan
