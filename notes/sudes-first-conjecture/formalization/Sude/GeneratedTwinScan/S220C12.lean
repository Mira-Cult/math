import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21516)) 462946349 462979117 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462946349 462979117).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21516 462946349 462979117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21517)) 462979117 463011885 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462979117 463011885).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21517 462979117 463011885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21518)) 463011885 463044653 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463011885 463044653).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21518 463011885 463044653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21519)) 463044653 463077421 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463044653 463077421).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21519 463044653 463077421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462946349 463011885).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 462946349 ≤ 462979117)
    (by decide : 462979117 ≤ 463011885) block0 block1

theorem join_0_1 : (twinPrimeSegment 463011885 463077421).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 463011885 ≤ 463044653)
    (by decide : 463044653 ≤ 463077421) block2 block3

theorem join_1_0 : (twinPrimeSegment 462946349 463077421).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 462946349 ≤ 463011885)
    (by decide : 463011885 ≤ 463077421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462946349 463077421).card = 435 := join_1_0

end S220C12
end Sude.GeneratedTwinScan
