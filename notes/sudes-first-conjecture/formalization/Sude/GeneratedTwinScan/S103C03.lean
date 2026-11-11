import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14711)) 216399917 216432685 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216399917 216432685).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14711 216399917 216432685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14712)) 216432685 216465453 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216432685 216465453).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14712 216432685 216465453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14713)) 216465453 216498221 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216465453 216498221).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14713 216465453 216498221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14714)) 216498221 216530989 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 216498221 216530989).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14714 216498221 216530989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216399917 216465453).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 216399917 ≤ 216432685)
    (by decide : 216432685 ≤ 216465453) block0 block1

theorem join_0_1 : (twinPrimeSegment 216465453 216530989).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 216465453 ≤ 216498221)
    (by decide : 216498221 ≤ 216530989) block2 block3

theorem join_1_0 : (twinPrimeSegment 216399917 216530989).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 216399917 ≤ 216465453)
    (by decide : 216465453 ≤ 216530989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216399917 216530989).card = 439 := join_1_0

end S103C03
end Sude.GeneratedTwinScan
