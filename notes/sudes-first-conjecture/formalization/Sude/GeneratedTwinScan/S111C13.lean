import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15314)) 234487853 234520621 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234487853 234520621).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15314 234487853 234520621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15315)) 234520621 234553389 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234520621 234553389).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15315 234520621 234553389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15316)) 234553389 234586157 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234553389 234586157).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15316 234553389 234586157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15317)) 234586157 234618925 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234586157 234618925).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15317 234586157 234618925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234487853 234553389).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 234487853 ≤ 234520621)
    (by decide : 234520621 ≤ 234553389) block0 block1

theorem join_0_1 : (twinPrimeSegment 234553389 234618925).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 234553389 ≤ 234586157)
    (by decide : 234586157 ≤ 234618925) block2 block3

theorem join_1_0 : (twinPrimeSegment 234487853 234618925).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 234487853 ≤ 234553389)
    (by decide : 234553389 ≤ 234618925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234487853 234618925).card = 435 := join_1_0

end S111C13
end Sude.GeneratedTwinScan
