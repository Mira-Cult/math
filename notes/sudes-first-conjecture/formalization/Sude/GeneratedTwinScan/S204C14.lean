import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20728)) 429654061 429686829 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 429654061 429686829).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20728 429654061 429686829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20729)) 429686829 429719597 = 87 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429686829 429719597).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20729 429686829 429719597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20730)) 429719597 429752365 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429719597 429752365).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20730 429719597 429752365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20731)) 429752365 429785133 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 429752365 429785133).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20731 429752365 429785133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 429654061 429719597).card = 183 := by
  simpa using combineTwinPrimeSegments (by decide : 429654061 ≤ 429686829)
    (by decide : 429686829 ≤ 429719597) block0 block1

theorem join_0_1 : (twinPrimeSegment 429719597 429785133).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 429719597 ≤ 429752365)
    (by decide : 429752365 ≤ 429785133) block2 block3

theorem join_1_0 : (twinPrimeSegment 429654061 429785133).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 429654061 ≤ 429719597)
    (by decide : 429719597 ≤ 429785133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 429654061 429785133).card = 412 := join_1_0

end S204C14
end Sude.GeneratedTwinScan
