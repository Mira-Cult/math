import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17337)) 300548141 300580909 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300548141 300580909).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17337 300548141 300580909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17338)) 300580909 300613677 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300580909 300613677).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17338 300580909 300613677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17339)) 300613677 300646445 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300613677 300646445).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17339 300613677 300646445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17340)) 300646445 300679213 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300646445 300679213).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17340 300646445 300679213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300548141 300613677).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 300548141 ≤ 300580909)
    (by decide : 300580909 ≤ 300613677) block0 block1

theorem join_0_1 : (twinPrimeSegment 300613677 300679213).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 300613677 ≤ 300646445)
    (by decide : 300646445 ≤ 300679213) block2 block3

theorem join_1_0 : (twinPrimeSegment 300548141 300679213).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 300548141 ≤ 300613677)
    (by decide : 300613677 ≤ 300679213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300548141 300679213).card = 463 := join_1_0

end S143C05
end Sude.GeneratedTwinScan
