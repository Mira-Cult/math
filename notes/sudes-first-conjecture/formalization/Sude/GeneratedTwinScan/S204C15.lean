import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20732)) 429785133 429817901 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 429785133 429817901).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20732 429785133 429817901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20732)) 429817901 429850669 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429817901 429850669).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20732 429817901 429850669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20733)) 429850669 429883437 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429850669 429883437).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20733 429850669 429883437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20734)) 429883437 429916205 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 429883437 429916205).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20734 429883437 429916205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 429785133 429850669).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 429785133 ≤ 429817901)
    (by decide : 429817901 ≤ 429850669) block0 block1

theorem join_0_1 : (twinPrimeSegment 429850669 429916205).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 429850669 ≤ 429883437)
    (by decide : 429883437 ≤ 429916205) block2 block3

theorem join_1_0 : (twinPrimeSegment 429785133 429916205).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 429785133 ≤ 429850669)
    (by decide : 429850669 ≤ 429916205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 429785133 429916205).card = 466 := join_1_0

end S204C15
end Sude.GeneratedTwinScan
