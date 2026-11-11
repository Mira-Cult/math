import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14644)) 214433837 214466605 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214433837 214466605).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14644 214433837 214466605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14645)) 214466605 214499373 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214466605 214499373).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14645 214466605 214499373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14646)) 214499373 214532141 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 214499373 214532141).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14646 214499373 214532141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14648)) 214532141 214564909 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214532141 214564909).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14648 214532141 214564909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214433837 214499373).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 214433837 ≤ 214466605)
    (by decide : 214466605 ≤ 214499373) block0 block1

theorem join_0_1 : (twinPrimeSegment 214499373 214564909).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 214499373 ≤ 214532141)
    (by decide : 214532141 ≤ 214564909) block2 block3

theorem join_1_0 : (twinPrimeSegment 214433837 214564909).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 214433837 ≤ 214499373)
    (by decide : 214499373 ≤ 214564909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214433837 214564909).card = 483 := join_1_0

end S102C04
end Sude.GeneratedTwinScan
