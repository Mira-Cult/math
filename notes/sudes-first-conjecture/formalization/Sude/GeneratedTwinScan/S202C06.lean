import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20602)) 424411181 424443949 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424411181 424443949).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20602 424411181 424443949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20602)) 424443949 424476717 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424443949 424476717).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20602 424443949 424476717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20603)) 424476717 424509485 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 424476717 424509485).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20603 424476717 424509485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20604)) 424509485 424542253 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 424509485 424542253).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20604 424509485 424542253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424411181 424476717).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 424411181 ≤ 424443949)
    (by decide : 424443949 ≤ 424476717) block0 block1

theorem join_0_1 : (twinPrimeSegment 424476717 424542253).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 424476717 ≤ 424509485)
    (by decide : 424509485 ≤ 424542253) block2 block3

theorem join_1_0 : (twinPrimeSegment 424411181 424542253).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 424411181 ≤ 424476717)
    (by decide : 424476717 ≤ 424542253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424411181 424542253).card = 450 := join_1_0

end S202C06
end Sude.GeneratedTwinScan
