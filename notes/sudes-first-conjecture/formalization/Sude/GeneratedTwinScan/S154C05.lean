import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17990)) 323616813 323649581 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323616813 323649581).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17990 323616813 323649581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17991)) 323649581 323682349 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323649581 323682349).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17991 323649581 323682349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17992)) 323682349 323715117 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323682349 323715117).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17992 323682349 323715117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17992)) 323715117 323747885 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323715117 323747885).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17992 323715117 323747885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323616813 323682349).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 323616813 ≤ 323649581)
    (by decide : 323649581 ≤ 323682349) block0 block1

theorem join_0_1 : (twinPrimeSegment 323682349 323747885).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 323682349 ≤ 323715117)
    (by decide : 323715117 ≤ 323747885) block2 block3

theorem join_1_0 : (twinPrimeSegment 323616813 323747885).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 323616813 ≤ 323682349)
    (by decide : 323682349 ≤ 323747885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323616813 323747885).card = 454 := join_1_0

end S154C05
end Sude.GeneratedTwinScan
