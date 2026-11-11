import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13124)) 172228653 172261421 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172228653 172261421).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13124 172228653 172261421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13126)) 172261421 172294189 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172261421 172294189).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13126 172261421 172294189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13127)) 172294189 172326957 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172294189 172326957).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13127 172294189 172326957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13128)) 172326957 172359725 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172326957 172359725).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13128 172326957 172359725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172228653 172294189).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 172228653 ≤ 172261421)
    (by decide : 172261421 ≤ 172294189) block0 block1

theorem join_0_1 : (twinPrimeSegment 172294189 172359725).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 172294189 ≤ 172326957)
    (by decide : 172326957 ≤ 172359725) block2 block3

theorem join_1_0 : (twinPrimeSegment 172228653 172359725).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 172228653 ≤ 172294189)
    (by decide : 172294189 ≤ 172359725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172228653 172359725).card = 499 := join_1_0

end S082C02
end Sude.GeneratedTwinScan
