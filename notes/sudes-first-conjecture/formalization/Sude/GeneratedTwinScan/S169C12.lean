import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18868)) 355991597 356024365 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 355991597 356024365).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18868 355991597 356024365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18869)) 356024365 356057133 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356024365 356057133).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18869 356024365 356057133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18870)) 356057133 356089901 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356057133 356089901).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18870 356057133 356089901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18871)) 356089901 356122669 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 356089901 356122669).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18871 356089901 356122669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 355991597 356057133).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 355991597 ≤ 356024365)
    (by decide : 356024365 ≤ 356057133) block0 block1

theorem join_0_1 : (twinPrimeSegment 356057133 356122669).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 356057133 ≤ 356089901)
    (by decide : 356089901 ≤ 356122669) block2 block3

theorem join_1_0 : (twinPrimeSegment 355991597 356122669).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 355991597 ≤ 356057133)
    (by decide : 356057133 ≤ 356122669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 355991597 356122669).card = 474 := join_1_0

end S169C12
end Sude.GeneratedTwinScan
