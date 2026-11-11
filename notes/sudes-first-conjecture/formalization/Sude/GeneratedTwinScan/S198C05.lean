import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20394)) 415891501 415924269 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 415891501 415924269).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20394 415891501 415924269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20395)) 415924269 415957037 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415924269 415957037).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20395 415924269 415957037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20395)) 415957037 415989805 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415957037 415989805).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20395 415957037 415989805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20396)) 415989805 416022573 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415989805 416022573).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20396 415989805 416022573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 415891501 415957037).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 415891501 ≤ 415924269)
    (by decide : 415924269 ≤ 415957037) block0 block1

theorem join_0_1 : (twinPrimeSegment 415957037 416022573).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 415957037 ≤ 415989805)
    (by decide : 415989805 ≤ 416022573) block2 block3

theorem join_1_0 : (twinPrimeSegment 415891501 416022573).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 415891501 ≤ 415957037)
    (by decide : 415957037 ≤ 416022573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 415891501 416022573).card = 438 := join_1_0

end S198C05
end Sude.GeneratedTwinScan
