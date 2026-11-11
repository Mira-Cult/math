import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20297)) 411959341 411992109 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 411959341 411992109).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20297 411959341 411992109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20298)) 411992109 412024877 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 411992109 412024877).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20298 411992109 412024877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20299)) 412024877 412057645 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412024877 412057645).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20299 412024877 412057645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20300)) 412057645 412090413 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412057645 412090413).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20300 412057645 412090413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 411959341 412024877).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 411959341 ≤ 411992109)
    (by decide : 411992109 ≤ 412024877) block0 block1

theorem join_0_1 : (twinPrimeSegment 412024877 412090413).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 412024877 ≤ 412057645)
    (by decide : 412057645 ≤ 412090413) block2 block3

theorem join_1_0 : (twinPrimeSegment 411959341 412090413).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 411959341 ≤ 412024877)
    (by decide : 412024877 ≤ 412090413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 411959341 412090413).card = 470 := join_1_0

end S196C07
end Sude.GeneratedTwinScan
