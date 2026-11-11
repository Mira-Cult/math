import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20242)) 409731117 409763885 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409731117 409763885).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20242 409731117 409763885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20243)) 409763885 409796653 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 409763885 409796653).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20243 409763885 409796653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20244)) 409796653 409829421 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409796653 409829421).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20244 409796653 409829421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20245)) 409829421 409862189 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409829421 409862189).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20245 409829421 409862189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409731117 409796653).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 409731117 ≤ 409763885)
    (by decide : 409763885 ≤ 409796653) block0 block1

theorem join_0_1 : (twinPrimeSegment 409796653 409862189).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 409796653 ≤ 409829421)
    (by decide : 409829421 ≤ 409862189) block2 block3

theorem join_1_0 : (twinPrimeSegment 409731117 409862189).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 409731117 ≤ 409796653)
    (by decide : 409796653 ≤ 409862189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409731117 409862189).card = 451 := join_1_0

end S195C06
end Sude.GeneratedTwinScan
