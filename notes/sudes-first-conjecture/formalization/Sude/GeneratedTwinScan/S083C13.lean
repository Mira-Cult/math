import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13258)) 175767597 175800365 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175767597 175800365).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13258 175767597 175800365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13260)) 175800365 175833133 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175800365 175833133).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13260 175800365 175833133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13261)) 175833133 175865901 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175833133 175865901).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13261 175833133 175865901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13262)) 175865901 175898669 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175865901 175898669).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13262 175865901 175898669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175767597 175833133).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 175767597 ≤ 175800365)
    (by decide : 175800365 ≤ 175833133) block0 block1

theorem join_0_1 : (twinPrimeSegment 175833133 175898669).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 175833133 ≤ 175865901)
    (by decide : 175865901 ≤ 175898669) block2 block3

theorem join_1_0 : (twinPrimeSegment 175767597 175898669).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 175767597 ≤ 175833133)
    (by decide : 175833133 ≤ 175898669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175767597 175898669).card = 516 := join_1_0

end S083C13
end Sude.GeneratedTwinScan
