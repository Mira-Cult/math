import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19287)) 371982381 372015149 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371982381 372015149).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19287 371982381 372015149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19288)) 372015149 372047917 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372015149 372047917).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19288 372015149 372047917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19289)) 372047917 372080685 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372047917 372080685).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19289 372047917 372080685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19290)) 372080685 372113453 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372080685 372113453).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19290 372080685 372113453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371982381 372047917).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 371982381 ≤ 372015149)
    (by decide : 372015149 ≤ 372047917) block0 block1

theorem join_0_1 : (twinPrimeSegment 372047917 372113453).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 372047917 ≤ 372080685)
    (by decide : 372080685 ≤ 372113453) block2 block3

theorem join_1_0 : (twinPrimeSegment 371982381 372113453).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 371982381 ≤ 372047917)
    (by decide : 372047917 ≤ 372113453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371982381 372113453).card = 450 := join_1_0

end S177C06
end Sude.GeneratedTwinScan
