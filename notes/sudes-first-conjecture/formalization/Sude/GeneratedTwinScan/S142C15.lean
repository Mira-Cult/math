import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17314)) 299761709 299794477 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 299761709 299794477).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17314 299761709 299794477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17315)) 299794477 299827245 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299794477 299827245).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17315 299794477 299827245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17316)) 299827245 299860013 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299827245 299860013).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17316 299827245 299860013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17317)) 299860013 299892781 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299860013 299892781).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17317 299860013 299892781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 299761709 299827245).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 299761709 ≤ 299794477)
    (by decide : 299794477 ≤ 299827245) block0 block1

theorem join_0_1 : (twinPrimeSegment 299827245 299892781).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 299827245 ≤ 299860013)
    (by decide : 299860013 ≤ 299892781) block2 block3

theorem join_1_0 : (twinPrimeSegment 299761709 299892781).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 299761709 ≤ 299827245)
    (by decide : 299827245 ≤ 299892781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 299761709 299892781).card = 434 := join_1_0

end S142C15
end Sude.GeneratedTwinScan
