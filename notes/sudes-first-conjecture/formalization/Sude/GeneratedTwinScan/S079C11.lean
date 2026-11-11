import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12928)) 167116845 167149613 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167116845 167149613).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12928 167116845 167149613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12929)) 167149613 167182381 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167149613 167182381).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12929 167149613 167182381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12931)) 167182381 167215149 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167182381 167215149).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12931 167182381 167215149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12932)) 167215149 167247917 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167215149 167247917).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12932 167215149 167247917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167116845 167182381).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 167116845 ≤ 167149613)
    (by decide : 167149613 ≤ 167182381) block0 block1

theorem join_0_1 : (twinPrimeSegment 167182381 167247917).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 167182381 ≤ 167215149)
    (by decide : 167215149 ≤ 167247917) block2 block3

theorem join_1_0 : (twinPrimeSegment 167116845 167247917).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 167116845 ≤ 167182381)
    (by decide : 167182381 ≤ 167247917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167116845 167247917).card = 507 := join_1_0

end S079C11
end Sude.GeneratedTwinScan
