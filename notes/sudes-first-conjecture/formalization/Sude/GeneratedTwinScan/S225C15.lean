import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21768)) 473825325 473858093 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473825325 473858093).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21768 473825325 473858093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21769)) 473858093 473890861 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473858093 473890861).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21769 473858093 473890861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21769)) 473890861 473923629 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 473890861 473923629).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21769 473890861 473923629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21770)) 473923629 473956397 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473923629 473956397).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21770 473923629 473956397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473825325 473890861).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 473825325 ≤ 473858093)
    (by decide : 473858093 ≤ 473890861) block0 block1

theorem join_0_1 : (twinPrimeSegment 473890861 473956397).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 473890861 ≤ 473923629)
    (by decide : 473923629 ≤ 473956397) block2 block3

theorem join_1_0 : (twinPrimeSegment 473825325 473956397).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 473825325 ≤ 473890861)
    (by decide : 473890861 ≤ 473956397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473825325 473956397).card = 425 := join_1_0

end S225C15
end Sude.GeneratedTwinScan
