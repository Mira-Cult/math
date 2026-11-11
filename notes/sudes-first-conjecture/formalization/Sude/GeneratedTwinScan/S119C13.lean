import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15852)) 251265069 251297837 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 251265069 251297837).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15852 251265069 251297837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15853)) 251297837 251330605 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 251297837 251330605).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15853 251297837 251330605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15854)) 251330605 251363373 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 251330605 251363373).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15854 251330605 251363373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15855)) 251363373 251396141 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 251363373 251396141).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15855 251363373 251396141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 251265069 251330605).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 251265069 ≤ 251297837)
    (by decide : 251297837 ≤ 251330605) block0 block1

theorem join_0_1 : (twinPrimeSegment 251330605 251396141).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 251330605 ≤ 251363373)
    (by decide : 251363373 ≤ 251396141) block2 block3

theorem join_1_0 : (twinPrimeSegment 251265069 251396141).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 251265069 ≤ 251330605)
    (by decide : 251330605 ≤ 251396141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 251265069 251396141).card = 481 := join_1_0

end S119C13
end Sude.GeneratedTwinScan
