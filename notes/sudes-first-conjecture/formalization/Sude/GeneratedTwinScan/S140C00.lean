import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17135)) 293601325 293634093 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293601325 293634093).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17135 293601325 293634093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17136)) 293634093 293666861 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 293634093 293666861).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17136 293634093 293666861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17137)) 293666861 293699629 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293666861 293699629).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17137 293666861 293699629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17138)) 293699629 293732397 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293699629 293732397).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17138 293699629 293732397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293601325 293666861).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 293634093)
    (by decide : 293634093 ≤ 293666861) block0 block1

theorem join_0_1 : (twinPrimeSegment 293666861 293732397).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 293666861 ≤ 293699629)
    (by decide : 293699629 ≤ 293732397) block2 block3

theorem join_1_0 : (twinPrimeSegment 293601325 293732397).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 293666861)
    (by decide : 293666861 ≤ 293732397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293601325 293732397).card = 455 := join_1_0

end S140C00
end Sude.GeneratedTwinScan
