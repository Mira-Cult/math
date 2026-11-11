import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14742)) 217317421 217350189 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217317421 217350189).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14742 217317421 217350189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14743)) 217350189 217382957 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217350189 217382957).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14743 217350189 217382957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14745)) 217382957 217415725 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217382957 217415725).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14745 217382957 217415725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14746)) 217415725 217448493 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217415725 217448493).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14746 217415725 217448493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217317421 217382957).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 217317421 ≤ 217350189)
    (by decide : 217350189 ≤ 217382957) block0 block1

theorem join_0_1 : (twinPrimeSegment 217382957 217448493).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 217382957 ≤ 217415725)
    (by decide : 217415725 ≤ 217448493) block2 block3

theorem join_1_0 : (twinPrimeSegment 217317421 217448493).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 217317421 ≤ 217382957)
    (by decide : 217382957 ≤ 217448493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217317421 217448493).card = 469 := join_1_0

end S103C10
end Sude.GeneratedTwinScan
