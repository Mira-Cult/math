import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13435)) 180486189 180518957 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180486189 180518957).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13435 180486189 180518957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13436)) 180518957 180551725 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180518957 180551725).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13436 180518957 180551725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13438)) 180551725 180584493 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180551725 180584493).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13438 180551725 180584493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13439)) 180584493 180617261 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180584493 180617261).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13439 180584493 180617261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180486189 180551725).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 180486189 ≤ 180518957)
    (by decide : 180518957 ≤ 180551725) block0 block1

theorem join_0_1 : (twinPrimeSegment 180551725 180617261).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 180551725 ≤ 180584493)
    (by decide : 180584493 ≤ 180617261) block2 block3

theorem join_1_0 : (twinPrimeSegment 180486189 180617261).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 180486189 ≤ 180551725)
    (by decide : 180551725 ≤ 180617261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180486189 180617261).card = 465 := join_1_0

end S086C01
end Sude.GeneratedTwinScan
