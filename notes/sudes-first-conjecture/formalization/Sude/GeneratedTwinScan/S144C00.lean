import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17378)) 301989933 302022701 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301989933 302022701).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17378 301989933 302022701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17379)) 302022701 302055469 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302022701 302055469).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17379 302022701 302055469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17380)) 302055469 302088237 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302055469 302088237).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17380 302055469 302088237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17381)) 302088237 302121005 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302088237 302121005).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17381 302088237 302121005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301989933 302055469).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 302022701)
    (by decide : 302022701 ≤ 302055469) block0 block1

theorem join_0_1 : (twinPrimeSegment 302055469 302121005).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 302055469 ≤ 302088237)
    (by decide : 302088237 ≤ 302121005) block2 block3

theorem join_1_0 : (twinPrimeSegment 301989933 302121005).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 302055469)
    (by decide : 302055469 ≤ 302121005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301989933 302121005).card = 475 := join_1_0

end S144C00
end Sude.GeneratedTwinScan
