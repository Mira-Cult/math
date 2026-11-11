import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22751)) 517603373 517636141 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 517603373 517636141).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22751 517603373 517636141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22752)) 517636141 517668909 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 517636141 517668909).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22752 517636141 517668909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22753)) 517668909 517701677 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 517668909 517701677).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22753 517668909 517701677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22753)) 517701677 517734445 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 517701677 517734445).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22753 517701677 517734445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 517603373 517668909).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 517603373 ≤ 517636141)
    (by decide : 517636141 ≤ 517668909) block0 block1

theorem join_0_1 : (twinPrimeSegment 517668909 517734445).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 517668909 ≤ 517701677)
    (by decide : 517701677 ≤ 517734445) block2 block3

theorem join_1_0 : (twinPrimeSegment 517603373 517734445).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 517603373 ≤ 517668909)
    (by decide : 517668909 ≤ 517734445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 517603373 517734445).card = 398 := join_1_0

end S246C13
end Sude.GeneratedTwinScan
