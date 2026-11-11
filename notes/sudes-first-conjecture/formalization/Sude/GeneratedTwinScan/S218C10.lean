import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21413)) 458489901 458522669 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458489901 458522669).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21413 458489901 458522669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21413)) 458522669 458555437 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458522669 458555437).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21413 458522669 458555437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21414)) 458555437 458588205 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458555437 458588205).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21414 458555437 458588205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21415)) 458588205 458620973 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458588205 458620973).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21415 458588205 458620973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458489901 458555437).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 458489901 ≤ 458522669)
    (by decide : 458522669 ≤ 458555437) block0 block1

theorem join_0_1 : (twinPrimeSegment 458555437 458620973).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 458555437 ≤ 458588205)
    (by decide : 458588205 ≤ 458620973) block2 block3

theorem join_1_0 : (twinPrimeSegment 458489901 458620973).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 458489901 ≤ 458555437)
    (by decide : 458555437 ≤ 458620973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458489901 458620973).card = 427 := join_1_0

end S218C10
end Sude.GeneratedTwinScan
