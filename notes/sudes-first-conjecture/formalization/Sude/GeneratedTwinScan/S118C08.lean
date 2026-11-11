import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15765)) 248512557 248545325 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248512557 248545325).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15765 248512557 248545325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15766)) 248545325 248578093 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248545325 248578093).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15766 248545325 248578093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15767)) 248578093 248610861 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248578093 248610861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15767 248578093 248610861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15768)) 248610861 248643629 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248610861 248643629).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15768 248610861 248643629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248512557 248578093).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 248512557 ≤ 248545325)
    (by decide : 248545325 ≤ 248578093) block0 block1

theorem join_0_1 : (twinPrimeSegment 248578093 248643629).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 248578093 ≤ 248610861)
    (by decide : 248610861 ≤ 248643629) block2 block3

theorem join_1_0 : (twinPrimeSegment 248512557 248643629).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 248512557 ≤ 248578093)
    (by decide : 248578093 ≤ 248643629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248512557 248643629).card = 435 := join_1_0

end S118C08
end Sude.GeneratedTwinScan
