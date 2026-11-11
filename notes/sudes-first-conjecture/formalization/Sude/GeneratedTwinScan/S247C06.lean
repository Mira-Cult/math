import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22777)) 518783021 518815789 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 518783021 518815789).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22777 518783021 518815789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22778)) 518815789 518848557 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 518815789 518848557).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22778 518815789 518848557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22778)) 518848557 518881325 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 518848557 518881325).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22778 518848557 518881325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22779)) 518881325 518914093 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 518881325 518914093).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22779 518881325 518914093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 518783021 518848557).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 518783021 ≤ 518815789)
    (by decide : 518815789 ≤ 518848557) block0 block1

theorem join_0_1 : (twinPrimeSegment 518848557 518914093).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 518848557 ≤ 518881325)
    (by decide : 518881325 ≤ 518914093) block2 block3

theorem join_1_0 : (twinPrimeSegment 518783021 518914093).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 518783021 ≤ 518848557)
    (by decide : 518848557 ≤ 518914093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 518783021 518914093).card = 422 := join_1_0

end S247C06
end Sude.GeneratedTwinScan
