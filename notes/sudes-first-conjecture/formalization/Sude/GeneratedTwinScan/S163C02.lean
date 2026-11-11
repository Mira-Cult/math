import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18496)) 342097965 342130733 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 342097965 342130733).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18496 342097965 342130733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18497)) 342130733 342163501 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 342130733 342163501).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18497 342130733 342163501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18498)) 342163501 342196269 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342163501 342196269).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18498 342163501 342196269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18499)) 342196269 342229037 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342196269 342229037).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18499 342196269 342229037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 342097965 342163501).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 342097965 ≤ 342130733)
    (by decide : 342130733 ≤ 342163501) block0 block1

theorem join_0_1 : (twinPrimeSegment 342163501 342229037).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 342163501 ≤ 342196269)
    (by decide : 342196269 ≤ 342229037) block2 block3

theorem join_1_0 : (twinPrimeSegment 342097965 342229037).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 342097965 ≤ 342163501)
    (by decide : 342163501 ≤ 342229037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 342097965 342229037).card = 406 := join_1_0

end S163C02
end Sude.GeneratedTwinScan
