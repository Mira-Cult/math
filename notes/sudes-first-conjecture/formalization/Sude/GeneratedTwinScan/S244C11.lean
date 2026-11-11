import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22653)) 513146925 513179693 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513146925 513179693).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22653 513146925 513179693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22654)) 513179693 513212461 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513179693 513212461).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22654 513179693 513212461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22654)) 513212461 513245229 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513212461 513245229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22654 513212461 513245229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22655)) 513245229 513277997 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513245229 513277997).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22655 513245229 513277997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513146925 513212461).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 513146925 ≤ 513179693)
    (by decide : 513179693 ≤ 513212461) block0 block1

theorem join_0_1 : (twinPrimeSegment 513212461 513277997).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 513212461 ≤ 513245229)
    (by decide : 513245229 ≤ 513277997) block2 block3

theorem join_1_0 : (twinPrimeSegment 513146925 513277997).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 513146925 ≤ 513212461)
    (by decide : 513212461 ≤ 513277997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513146925 513277997).card = 427 := join_1_0

end S244C11
end Sude.GeneratedTwinScan
