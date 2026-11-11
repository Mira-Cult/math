import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14760)) 217841709 217874477 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217841709 217874477).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14760 217841709 217874477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14761)) 217874477 217907245 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217874477 217907245).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14761 217874477 217907245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14762)) 217907245 217940013 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217907245 217940013).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14762 217907245 217940013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14763)) 217940013 217972781 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217940013 217972781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14763 217940013 217972781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217841709 217907245).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 217841709 ≤ 217874477)
    (by decide : 217874477 ≤ 217907245) block0 block1

theorem join_0_1 : (twinPrimeSegment 217907245 217972781).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 217907245 ≤ 217940013)
    (by decide : 217940013 ≤ 217972781) block2 block3

theorem join_1_0 : (twinPrimeSegment 217841709 217972781).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 217841709 ≤ 217907245)
    (by decide : 217907245 ≤ 217972781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217841709 217972781).card = 442 := join_1_0

end S103C14
end Sude.GeneratedTwinScan
