import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15723)) 247201837 247234605 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247201837 247234605).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15723 247201837 247234605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15724)) 247234605 247267373 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 247234605 247267373).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15724 247234605 247267373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15725)) 247267373 247300141 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247267373 247300141).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15725 247267373 247300141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15726)) 247300141 247332909 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247300141 247332909).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15726 247300141 247332909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247201837 247267373).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 247201837 ≤ 247234605)
    (by decide : 247234605 ≤ 247267373) block0 block1

theorem join_0_1 : (twinPrimeSegment 247267373 247332909).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 247267373 ≤ 247300141)
    (by decide : 247300141 ≤ 247332909) block2 block3

theorem join_1_0 : (twinPrimeSegment 247201837 247332909).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 247201837 ≤ 247267373)
    (by decide : 247267373 ≤ 247332909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247201837 247332909).card = 468 := join_1_0

end S117C14
end Sude.GeneratedTwinScan
