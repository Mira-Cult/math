import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13372)) 178782253 178815021 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 178782253 178815021).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13372 178782253 178815021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13373)) 178815021 178847789 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178815021 178847789).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13373 178815021 178847789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13374)) 178847789 178880557 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178847789 178880557).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13374 178847789 178880557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13375)) 178880557 178913325 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 178880557 178913325).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13375 178880557 178913325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 178782253 178847789).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 178782253 ≤ 178815021)
    (by decide : 178815021 ≤ 178847789) block0 block1

theorem join_0_1 : (twinPrimeSegment 178847789 178913325).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 178847789 ≤ 178880557)
    (by decide : 178880557 ≤ 178913325) block2 block3

theorem join_1_0 : (twinPrimeSegment 178782253 178913325).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 178782253 ≤ 178847789)
    (by decide : 178847789 ≤ 178913325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 178782253 178913325).card = 478 := join_1_0

end S085C04
end Sude.GeneratedTwinScan
