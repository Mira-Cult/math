import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22496)) 506069037 506101805 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506069037 506101805).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22496 506069037 506101805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22497)) 506101805 506134573 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 506101805 506134573).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22497 506101805 506134573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22498)) 506134573 506167341 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506134573 506167341).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22498 506134573 506167341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22498)) 506167341 506200109 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506167341 506200109).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22498 506167341 506200109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506069037 506134573).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 506069037 ≤ 506101805)
    (by decide : 506101805 ≤ 506134573) block0 block1

theorem join_0_1 : (twinPrimeSegment 506134573 506200109).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 506134573 ≤ 506167341)
    (by decide : 506167341 ≤ 506200109) block2 block3

theorem join_1_0 : (twinPrimeSegment 506069037 506200109).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 506069037 ≤ 506134573)
    (by decide : 506134573 ≤ 506200109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506069037 506200109).card = 456 := join_1_0

end S241C05
end Sude.GeneratedTwinScan
