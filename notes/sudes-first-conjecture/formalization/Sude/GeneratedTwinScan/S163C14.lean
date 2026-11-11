import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18539)) 343670829 343703597 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 343670829 343703597).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18539 343670829 343703597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18540)) 343703597 343736365 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 343703597 343736365).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18540 343703597 343736365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18541)) 343736365 343769133 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 343736365 343769133).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18541 343736365 343769133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18541)) 343769133 343801901 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 343769133 343801901).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18541 343769133 343801901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 343670829 343736365).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 343670829 ≤ 343703597)
    (by decide : 343703597 ≤ 343736365) block0 block1

theorem join_0_1 : (twinPrimeSegment 343736365 343801901).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 343736365 ≤ 343769133)
    (by decide : 343769133 ≤ 343801901) block2 block3

theorem join_1_0 : (twinPrimeSegment 343670829 343801901).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 343670829 ≤ 343736365)
    (by decide : 343736365 ≤ 343801901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 343670829 343801901).card = 460 := join_1_0

end S163C14
end Sude.GeneratedTwinScan
