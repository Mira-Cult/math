import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21671)) 469631021 469663789 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469631021 469663789).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21671 469631021 469663789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21672)) 469663789 469696557 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469663789 469696557).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21672 469663789 469696557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21673)) 469696557 469729325 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469696557 469729325).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21673 469696557 469729325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21673)) 469729325 469762093 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469729325 469762093).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21673 469729325 469762093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469631021 469696557).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 469631021 ≤ 469663789)
    (by decide : 469663789 ≤ 469696557) block0 block1

theorem join_0_1 : (twinPrimeSegment 469696557 469762093).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 469696557 ≤ 469729325)
    (by decide : 469729325 ≤ 469762093) block2 block3

theorem join_1_0 : (twinPrimeSegment 469631021 469762093).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 469631021 ≤ 469696557)
    (by decide : 469696557 ≤ 469762093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469631021 469762093).card = 434 := join_1_0

end S223C15
end Sude.GeneratedTwinScan
