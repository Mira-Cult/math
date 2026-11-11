import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20945)) 438698029 438730797 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438698029 438730797).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20945 438698029 438730797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20946)) 438730797 438763565 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438730797 438763565).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20946 438730797 438763565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20947)) 438763565 438796333 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438763565 438796333).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20947 438763565 438796333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20948)) 438796333 438829101 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438796333 438829101).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20948 438796333 438829101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438698029 438763565).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 438698029 ≤ 438730797)
    (by decide : 438730797 ≤ 438763565) block0 block1

theorem join_0_1 : (twinPrimeSegment 438763565 438829101).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 438763565 ≤ 438796333)
    (by decide : 438796333 ≤ 438829101) block2 block3

theorem join_1_0 : (twinPrimeSegment 438698029 438829101).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 438698029 ≤ 438763565)
    (by decide : 438763565 ≤ 438829101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438698029 438829101).card = 460 := join_1_0

end S209C03
end Sude.GeneratedTwinScan
