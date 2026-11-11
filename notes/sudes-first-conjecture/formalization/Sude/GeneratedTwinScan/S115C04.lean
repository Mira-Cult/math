import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15547)) 241696813 241729581 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241696813 241729581).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15547 241696813 241729581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15548)) 241729581 241762349 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241729581 241762349).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15548 241729581 241762349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15549)) 241762349 241795117 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241762349 241795117).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15549 241762349 241795117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15550)) 241795117 241827885 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241795117 241827885).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15550 241795117 241827885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241696813 241762349).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 241696813 ≤ 241729581)
    (by decide : 241729581 ≤ 241762349) block0 block1

theorem join_0_1 : (twinPrimeSegment 241762349 241827885).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 241762349 ≤ 241795117)
    (by decide : 241795117 ≤ 241827885) block2 block3

theorem join_1_0 : (twinPrimeSegment 241696813 241827885).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 241696813 ≤ 241762349)
    (by decide : 241762349 ≤ 241827885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241696813 241827885).card = 465 := join_1_0

end S115C04
end Sude.GeneratedTwinScan
