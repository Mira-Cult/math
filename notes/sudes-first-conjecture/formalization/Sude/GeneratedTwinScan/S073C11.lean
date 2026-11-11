import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12432)) 154533933 154566701 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154533933 154566701).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12432 154533933 154566701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12433)) 154566701 154599469 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154566701 154599469).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12433 154566701 154599469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12435)) 154599469 154632237 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154599469 154632237).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12435 154599469 154632237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12436)) 154632237 154665005 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154632237 154665005).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12436 154632237 154665005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154533933 154599469).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 154533933 ≤ 154566701)
    (by decide : 154566701 ≤ 154599469) block0 block1

theorem join_0_1 : (twinPrimeSegment 154599469 154665005).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 154599469 ≤ 154632237)
    (by decide : 154632237 ≤ 154665005) block2 block3

theorem join_1_0 : (twinPrimeSegment 154533933 154665005).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 154533933 ≤ 154599469)
    (by decide : 154599469 ≤ 154665005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154533933 154665005).card = 475 := join_1_0

end S073C11
end Sude.GeneratedTwinScan
