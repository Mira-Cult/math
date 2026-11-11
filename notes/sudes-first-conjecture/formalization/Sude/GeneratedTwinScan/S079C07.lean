import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12908)) 166592557 166625325 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166592557 166625325).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12908 166592557 166625325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12909)) 166625325 166658093 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166625325 166658093).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12909 166625325 166658093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12910)) 166658093 166690861 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166658093 166690861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12910 166658093 166690861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12912)) 166690861 166723629 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166690861 166723629).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12912 166690861 166723629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166592557 166658093).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 166592557 ≤ 166625325)
    (by decide : 166625325 ≤ 166658093) block0 block1

theorem join_0_1 : (twinPrimeSegment 166658093 166723629).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 166658093 ≤ 166690861)
    (by decide : 166690861 ≤ 166723629) block2 block3

theorem join_1_0 : (twinPrimeSegment 166592557 166723629).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 166592557 ≤ 166658093)
    (by decide : 166658093 ≤ 166723629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166592557 166723629).card = 504 := join_1_0

end S079C07
end Sude.GeneratedTwinScan
