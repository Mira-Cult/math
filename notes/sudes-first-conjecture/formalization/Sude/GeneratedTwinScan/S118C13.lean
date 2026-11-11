import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15786)) 249167917 249200685 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 249167917 249200685).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15786 249167917 249200685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15787)) 249200685 249233453 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 249200685 249233453).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15787 249200685 249233453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15788)) 249233453 249266221 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 249233453 249266221).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15788 249233453 249266221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15789)) 249266221 249298989 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 249266221 249298989).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15789 249266221 249298989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 249167917 249233453).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 249167917 ≤ 249200685)
    (by decide : 249200685 ≤ 249233453) block0 block1

theorem join_0_1 : (twinPrimeSegment 249233453 249298989).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 249233453 ≤ 249266221)
    (by decide : 249266221 ≤ 249298989) block2 block3

theorem join_1_0 : (twinPrimeSegment 249167917 249298989).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 249167917 ≤ 249233453)
    (by decide : 249233453 ≤ 249298989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 249167917 249298989).card = 454 := join_1_0

end S118C13
end Sude.GeneratedTwinScan
