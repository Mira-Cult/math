import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14586)) 212729901 212762669 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212729901 212762669).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14586 212729901 212762669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14587)) 212762669 212795437 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212762669 212795437).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14587 212762669 212795437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14588)) 212795437 212828205 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212795437 212828205).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14588 212795437 212828205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14589)) 212828205 212860973 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212828205 212860973).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14589 212828205 212860973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212729901 212795437).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 212729901 ≤ 212762669)
    (by decide : 212762669 ≤ 212795437) block0 block1

theorem join_0_1 : (twinPrimeSegment 212795437 212860973).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 212795437 ≤ 212828205)
    (by decide : 212828205 ≤ 212860973) block2 block3

theorem join_1_0 : (twinPrimeSegment 212729901 212860973).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 212729901 ≤ 212795437)
    (by decide : 212795437 ≤ 212860973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212729901 212860973).card = 466 := join_1_0

end S101C07
end Sude.GeneratedTwinScan
