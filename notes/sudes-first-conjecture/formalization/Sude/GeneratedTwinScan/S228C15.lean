import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21912)) 480116781 480149549 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 480116781 480149549).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21912 480116781 480149549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21913)) 480149549 480182317 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 480149549 480182317).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21913 480149549 480182317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21913)) 480182317 480215085 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 480182317 480215085).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21913 480182317 480215085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21914)) 480215085 480247853 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 480215085 480247853).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21914 480215085 480247853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 480116781 480182317).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 480116781 ≤ 480149549)
    (by decide : 480149549 ≤ 480182317) block0 block1

theorem join_0_1 : (twinPrimeSegment 480182317 480247853).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 480182317 ≤ 480215085)
    (by decide : 480215085 ≤ 480247853) block2 block3

theorem join_1_0 : (twinPrimeSegment 480116781 480247853).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 480116781 ≤ 480182317)
    (by decide : 480182317 ≤ 480247853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 480116781 480247853).card = 422 := join_1_0

end S228C15
end Sude.GeneratedTwinScan
