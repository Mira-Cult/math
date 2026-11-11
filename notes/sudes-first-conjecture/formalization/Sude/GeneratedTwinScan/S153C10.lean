import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17950)) 322175021 322207789 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322175021 322207789).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17950 322175021 322207789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17951)) 322207789 322240557 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322207789 322240557).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17951 322207789 322240557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17951)) 322240557 322273325 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 322240557 322273325).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17951 322240557 322273325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17952)) 322273325 322306093 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322273325 322306093).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17952 322273325 322306093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322175021 322240557).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 322175021 ≤ 322207789)
    (by decide : 322207789 ≤ 322240557) block0 block1

theorem join_0_1 : (twinPrimeSegment 322240557 322306093).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 322240557 ≤ 322273325)
    (by decide : 322273325 ≤ 322306093) block2 block3

theorem join_1_0 : (twinPrimeSegment 322175021 322306093).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 322175021 ≤ 322240557)
    (by decide : 322240557 ≤ 322306093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322175021 322306093).card = 449 := join_1_0

end S153C10
end Sude.GeneratedTwinScan
