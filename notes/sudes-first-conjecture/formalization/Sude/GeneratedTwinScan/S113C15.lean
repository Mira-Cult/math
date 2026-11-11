import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15458)) 238944301 238977069 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238944301 238977069).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15458 238944301 238977069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15459)) 238977069 239009837 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238977069 239009837).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15459 238977069 239009837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15461)) 239009837 239042605 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239009837 239042605).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15461 239009837 239042605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15462)) 239042605 239075373 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239042605 239075373).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15462 239042605 239075373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238944301 239009837).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 238944301 ≤ 238977069)
    (by decide : 238977069 ≤ 239009837) block0 block1

theorem join_0_1 : (twinPrimeSegment 239009837 239075373).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 239009837 ≤ 239042605)
    (by decide : 239042605 ≤ 239075373) block2 block3

theorem join_1_0 : (twinPrimeSegment 238944301 239075373).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 238944301 ≤ 239009837)
    (by decide : 239009837 ≤ 239075373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238944301 239075373).card = 448 := join_1_0

end S113C15
end Sude.GeneratedTwinScan
