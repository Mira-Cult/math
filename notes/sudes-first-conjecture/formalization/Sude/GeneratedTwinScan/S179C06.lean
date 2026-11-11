import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19396)) 376176685 376209453 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376176685 376209453).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19396 376176685 376209453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19396)) 376209453 376242221 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376209453 376242221).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19396 376209453 376242221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19397)) 376242221 376274989 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376242221 376274989).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19397 376242221 376274989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19398)) 376274989 376307757 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376274989 376307757).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19398 376274989 376307757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376176685 376242221).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 376176685 ≤ 376209453)
    (by decide : 376209453 ≤ 376242221) block0 block1

theorem join_0_1 : (twinPrimeSegment 376242221 376307757).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 376242221 ≤ 376274989)
    (by decide : 376274989 ≤ 376307757) block2 block3

theorem join_1_0 : (twinPrimeSegment 376176685 376307757).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 376176685 ≤ 376242221)
    (by decide : 376242221 ≤ 376307757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376176685 376307757).card = 463 := join_1_0

end S179C06
end Sude.GeneratedTwinScan
