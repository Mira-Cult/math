import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16344)) 267124781 267157549 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 267124781 267157549).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16344 267124781 267157549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16345)) 267157549 267190317 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 267157549 267190317).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16345 267157549 267190317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16346)) 267190317 267223085 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 267190317 267223085).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16346 267190317 267223085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16347)) 267223085 267255853 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 267223085 267255853).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16347 267223085 267255853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 267124781 267190317).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 267124781 ≤ 267157549)
    (by decide : 267157549 ≤ 267190317) block0 block1

theorem join_0_1 : (twinPrimeSegment 267190317 267255853).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 267190317 ≤ 267223085)
    (by decide : 267223085 ≤ 267255853) block2 block3

theorem join_1_0 : (twinPrimeSegment 267124781 267255853).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 267124781 ≤ 267190317)
    (by decide : 267190317 ≤ 267255853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 267124781 267255853).card = 467 := join_1_0

end S127C06
end Sude.GeneratedTwinScan
