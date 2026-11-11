import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18471)) 341180461 341213229 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341180461 341213229).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18471 341180461 341213229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18472)) 341213229 341245997 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341213229 341245997).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18472 341213229 341245997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18473)) 341245997 341278765 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 341245997 341278765).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18473 341245997 341278765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18474)) 341278765 341311533 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341278765 341311533).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18474 341278765 341311533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341180461 341245997).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 341180461 ≤ 341213229)
    (by decide : 341213229 ≤ 341245997) block0 block1

theorem join_0_1 : (twinPrimeSegment 341245997 341311533).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 341245997 ≤ 341278765)
    (by decide : 341278765 ≤ 341311533) block2 block3

theorem join_1_0 : (twinPrimeSegment 341180461 341311533).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 341180461 ≤ 341245997)
    (by decide : 341245997 ≤ 341311533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341180461 341311533).card = 433 := join_1_0

end S162C11
end Sude.GeneratedTwinScan
