import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19641)) 385744941 385777709 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385744941 385777709).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19641 385744941 385777709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19642)) 385777709 385810477 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385777709 385810477).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19642 385777709 385810477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19642)) 385810477 385843245 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385810477 385843245).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19642 385810477 385843245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19643)) 385843245 385876013 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385843245 385876013).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19643 385843245 385876013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385744941 385810477).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 385744941 ≤ 385777709)
    (by decide : 385777709 ≤ 385810477) block0 block1

theorem join_0_1 : (twinPrimeSegment 385810477 385876013).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 385810477 ≤ 385843245)
    (by decide : 385843245 ≤ 385876013) block2 block3

theorem join_1_0 : (twinPrimeSegment 385744941 385876013).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 385744941 ≤ 385810477)
    (by decide : 385810477 ≤ 385876013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385744941 385876013).card = 465 := join_1_0

end S183C15
end Sude.GeneratedTwinScan
