import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14400)) 207355949 207388717 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 207355949 207388717).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14400 207355949 207388717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14402)) 207388717 207421485 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 207388717 207421485).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14402 207388717 207421485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14403)) 207421485 207454253 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 207421485 207454253).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14403 207421485 207454253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14404)) 207454253 207487021 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 207454253 207487021).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14404 207454253 207487021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 207355949 207421485).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 207355949 ≤ 207388717)
    (by decide : 207388717 ≤ 207421485) block0 block1

theorem join_0_1 : (twinPrimeSegment 207421485 207487021).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 207421485 ≤ 207454253)
    (by decide : 207454253 ≤ 207487021) block2 block3

theorem join_1_0 : (twinPrimeSegment 207355949 207487021).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 207355949 ≤ 207421485)
    (by decide : 207421485 ≤ 207487021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 207355949 207487021).card = 445 := join_1_0

end S098C14
end Sude.GeneratedTwinScan
