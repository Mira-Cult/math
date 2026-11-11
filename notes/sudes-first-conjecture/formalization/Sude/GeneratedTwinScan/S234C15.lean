import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22197)) 492699693 492732461 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492699693 492732461).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22197 492699693 492732461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22198)) 492732461 492765229 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492732461 492765229).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22198 492732461 492765229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22199)) 492765229 492797997 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492765229 492797997).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22199 492765229 492797997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22199)) 492797997 492830765 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492797997 492830765).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22199 492797997 492830765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492699693 492765229).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 492699693 ≤ 492732461)
    (by decide : 492732461 ≤ 492765229) block0 block1

theorem join_0_1 : (twinPrimeSegment 492765229 492830765).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 492765229 ≤ 492797997)
    (by decide : 492797997 ≤ 492830765) block2 block3

theorem join_1_0 : (twinPrimeSegment 492699693 492830765).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 492699693 ≤ 492765229)
    (by decide : 492765229 ≤ 492830765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492699693 492830765).card = 436 := join_1_0

end S234C15
end Sude.GeneratedTwinScan
