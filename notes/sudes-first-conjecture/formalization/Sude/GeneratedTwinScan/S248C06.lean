import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22823)) 520880173 520912941 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 520880173 520912941).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22823 520880173 520912941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22824)) 520912941 520945709 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 520912941 520945709).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22824 520912941 520945709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22824)) 520945709 520978477 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520945709 520978477).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22824 520945709 520978477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22825)) 520978477 521011245 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520978477 521011245).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22825 520978477 521011245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 520880173 520945709).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 520880173 ≤ 520912941)
    (by decide : 520912941 ≤ 520945709) block0 block1

theorem join_0_1 : (twinPrimeSegment 520945709 521011245).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 520945709 ≤ 520978477)
    (by decide : 520978477 ≤ 521011245) block2 block3

theorem join_1_0 : (twinPrimeSegment 520880173 521011245).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 520880173 ≤ 520945709)
    (by decide : 520945709 ≤ 521011245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 520880173 521011245).card = 425 := join_1_0

end S248C06
end Sude.GeneratedTwinScan
