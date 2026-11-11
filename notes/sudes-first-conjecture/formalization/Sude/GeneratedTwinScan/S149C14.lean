import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17729)) 314310701 314343469 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314310701 314343469).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17729 314310701 314343469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17730)) 314343469 314376237 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314343469 314376237).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17730 314343469 314376237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17731)) 314376237 314409005 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314376237 314409005).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17731 314376237 314409005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17732)) 314409005 314441773 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314409005 314441773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17732 314409005 314441773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314310701 314376237).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 314310701 ≤ 314343469)
    (by decide : 314343469 ≤ 314376237) block0 block1

theorem join_0_1 : (twinPrimeSegment 314376237 314441773).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 314376237 ≤ 314409005)
    (by decide : 314409005 ≤ 314441773) block2 block3

theorem join_1_0 : (twinPrimeSegment 314310701 314441773).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 314310701 ≤ 314376237)
    (by decide : 314376237 ≤ 314441773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314310701 314441773).card = 489 := join_1_0

end S149C14
end Sude.GeneratedTwinScan
