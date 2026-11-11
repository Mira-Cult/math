import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17939)) 321781805 321814573 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 321781805 321814573).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17939 321781805 321814573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17940)) 321814573 321847341 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321814573 321847341).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17940 321814573 321847341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17941)) 321847341 321880109 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321847341 321880109).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17941 321847341 321880109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17941)) 321880109 321912877 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 321880109 321912877).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17941 321880109 321912877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 321781805 321847341).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 321781805 ≤ 321814573)
    (by decide : 321814573 ≤ 321847341) block0 block1

theorem join_0_1 : (twinPrimeSegment 321847341 321912877).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 321847341 ≤ 321880109)
    (by decide : 321880109 ≤ 321912877) block2 block3

theorem join_1_0 : (twinPrimeSegment 321781805 321912877).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 321781805 ≤ 321847341)
    (by decide : 321847341 ≤ 321912877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 321781805 321912877).card = 429 := join_1_0

end S153C07
end Sude.GeneratedTwinScan
