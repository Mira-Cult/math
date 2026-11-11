import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20892)) 436469805 436502573 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436469805 436502573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20892 436469805 436502573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20893)) 436502573 436535341 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436502573 436535341).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20893 436502573 436535341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20894)) 436535341 436568109 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436535341 436568109).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20894 436535341 436568109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20894)) 436568109 436600877 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436568109 436600877).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20894 436568109 436600877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436469805 436535341).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 436469805 ≤ 436502573)
    (by decide : 436502573 ≤ 436535341) block0 block1

theorem join_0_1 : (twinPrimeSegment 436535341 436600877).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 436535341 ≤ 436568109)
    (by decide : 436568109 ≤ 436600877) block2 block3

theorem join_1_0 : (twinPrimeSegment 436469805 436600877).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 436469805 ≤ 436535341)
    (by decide : 436535341 ≤ 436600877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436469805 436600877).card = 439 := join_1_0

end S208C02
end Sude.GeneratedTwinScan
