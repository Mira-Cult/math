import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22604)) 510918701 510951469 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510918701 510951469).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22604 510918701 510951469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22604)) 510951469 510984237 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510951469 510984237).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22604 510951469 510984237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22605)) 510984237 511017005 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510984237 511017005).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22605 510984237 511017005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22606)) 511017005 511049773 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511017005 511049773).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22606 511017005 511049773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510918701 510984237).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 510918701 ≤ 510951469)
    (by decide : 510951469 ≤ 510984237) block0 block1

theorem join_0_1 : (twinPrimeSegment 510984237 511049773).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 510984237 ≤ 511017005)
    (by decide : 511017005 ≤ 511049773) block2 block3

theorem join_1_0 : (twinPrimeSegment 510918701 511049773).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 510918701 ≤ 510984237)
    (by decide : 510984237 ≤ 511049773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510918701 511049773).card = 434 := join_1_0

end S243C10
end Sude.GeneratedTwinScan
