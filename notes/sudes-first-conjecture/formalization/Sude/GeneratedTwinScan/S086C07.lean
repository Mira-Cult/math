import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13464)) 181272621 181305389 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181272621 181305389).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13464 181272621 181305389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13466)) 181305389 181338157 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181305389 181338157).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13466 181305389 181338157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13467)) 181338157 181370925 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181338157 181370925).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13467 181338157 181370925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13468)) 181370925 181403693 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181370925 181403693).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13468 181370925 181403693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181272621 181338157).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 181272621 ≤ 181305389)
    (by decide : 181305389 ≤ 181338157) block0 block1

theorem join_0_1 : (twinPrimeSegment 181338157 181403693).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 181338157 ≤ 181370925)
    (by decide : 181370925 ≤ 181403693) block2 block3

theorem join_1_0 : (twinPrimeSegment 181272621 181403693).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 181272621 ≤ 181338157)
    (by decide : 181338157 ≤ 181403693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181272621 181403693).card = 473 := join_1_0

end S086C07
end Sude.GeneratedTwinScan
