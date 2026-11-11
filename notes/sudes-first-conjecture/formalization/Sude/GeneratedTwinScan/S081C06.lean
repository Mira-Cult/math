import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13064)) 170655789 170688557 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170655789 170688557).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13064 170655789 170688557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13066)) 170688557 170721325 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170688557 170721325).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13066 170688557 170721325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13067)) 170721325 170754093 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170721325 170754093).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13067 170721325 170754093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13068)) 170754093 170786861 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 170754093 170786861).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13068 170754093 170786861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170655789 170721325).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 170655789 ≤ 170688557)
    (by decide : 170688557 ≤ 170721325) block0 block1

theorem join_0_1 : (twinPrimeSegment 170721325 170786861).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 170721325 ≤ 170754093)
    (by decide : 170754093 ≤ 170786861) block2 block3

theorem join_1_0 : (twinPrimeSegment 170655789 170786861).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 170655789 ≤ 170721325)
    (by decide : 170721325 ≤ 170786861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170655789 170786861).card = 483 := join_1_0

end S081C06
end Sude.GeneratedTwinScan
