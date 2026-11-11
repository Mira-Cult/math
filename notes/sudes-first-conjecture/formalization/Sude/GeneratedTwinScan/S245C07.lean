import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22688)) 514719789 514752557 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514719789 514752557).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22688 514719789 514752557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22688)) 514752557 514785325 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514752557 514785325).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22688 514752557 514785325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22689)) 514785325 514818093 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514785325 514818093).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22689 514785325 514818093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22690)) 514818093 514850861 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514818093 514850861).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22690 514818093 514850861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514719789 514785325).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 514719789 ≤ 514752557)
    (by decide : 514752557 ≤ 514785325) block0 block1

theorem join_0_1 : (twinPrimeSegment 514785325 514850861).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 514785325 ≤ 514818093)
    (by decide : 514818093 ≤ 514850861) block2 block3

theorem join_1_0 : (twinPrimeSegment 514719789 514850861).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 514719789 ≤ 514785325)
    (by decide : 514785325 ≤ 514850861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514719789 514850861).card = 402 := join_1_0

end S245C07
end Sude.GeneratedTwinScan
