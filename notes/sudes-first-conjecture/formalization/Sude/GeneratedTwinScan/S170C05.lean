import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18899)) 357171245 357204013 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357171245 357204013).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18899 357171245 357204013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18900)) 357204013 357236781 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357204013 357236781).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18900 357204013 357236781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18901)) 357236781 357269549 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357236781 357269549).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18901 357236781 357269549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18902)) 357269549 357302317 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357269549 357302317).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18902 357269549 357302317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357171245 357236781).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 357171245 ≤ 357204013)
    (by decide : 357204013 ≤ 357236781) block0 block1

theorem join_0_1 : (twinPrimeSegment 357236781 357302317).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 357236781 ≤ 357269549)
    (by decide : 357269549 ≤ 357302317) block2 block3

theorem join_1_0 : (twinPrimeSegment 357171245 357302317).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 357171245 ≤ 357236781)
    (by decide : 357236781 ≤ 357302317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357171245 357302317).card = 443 := join_1_0

end S170C05
end Sude.GeneratedTwinScan
