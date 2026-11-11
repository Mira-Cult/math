import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13239)) 175243309 175276077 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175243309 175276077).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13239 175243309 175276077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13240)) 175276077 175308845 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175276077 175308845).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13240 175276077 175308845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13241)) 175308845 175341613 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175308845 175341613).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13241 175308845 175341613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13242)) 175341613 175374381 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175341613 175374381).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13242 175341613 175374381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175243309 175308845).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 175243309 ≤ 175276077)
    (by decide : 175276077 ≤ 175308845) block0 block1

theorem join_0_1 : (twinPrimeSegment 175308845 175374381).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 175308845 ≤ 175341613)
    (by decide : 175341613 ≤ 175374381) block2 block3

theorem join_1_0 : (twinPrimeSegment 175243309 175374381).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 175243309 ≤ 175308845)
    (by decide : 175308845 ≤ 175374381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175243309 175374381).card = 483 := join_1_0

end S083C09
end Sude.GeneratedTwinScan
