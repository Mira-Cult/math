import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17476)) 305397805 305430573 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305397805 305430573).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17476 305397805 305430573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17477)) 305430573 305463341 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305430573 305463341).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17477 305430573 305463341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17478)) 305463341 305496109 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305463341 305496109).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17478 305463341 305496109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17479)) 305496109 305528877 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305496109 305528877).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17479 305496109 305528877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305397805 305463341).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 305397805 ≤ 305430573)
    (by decide : 305430573 ≤ 305463341) block0 block1

theorem join_0_1 : (twinPrimeSegment 305463341 305528877).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 305463341 ≤ 305496109)
    (by decide : 305496109 ≤ 305528877) block2 block3

theorem join_1_0 : (twinPrimeSegment 305397805 305528877).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 305397805 ≤ 305463341)
    (by decide : 305463341 ≤ 305528877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305397805 305528877).card = 442 := join_1_0

end S145C10
end Sude.GeneratedTwinScan
