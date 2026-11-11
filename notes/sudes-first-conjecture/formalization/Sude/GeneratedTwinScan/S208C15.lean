import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20933)) 438173741 438206509 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438173741 438206509).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20933 438173741 438206509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20934)) 438206509 438239277 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438206509 438239277).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20934 438206509 438239277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20934)) 438239277 438272045 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438239277 438272045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20934 438239277 438272045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20935)) 438272045 438304813 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438272045 438304813).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20935 438272045 438304813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438173741 438239277).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 438173741 ≤ 438206509)
    (by decide : 438206509 ≤ 438239277) block0 block1

theorem join_0_1 : (twinPrimeSegment 438239277 438304813).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 438239277 ≤ 438272045)
    (by decide : 438272045 ≤ 438304813) block2 block3

theorem join_1_0 : (twinPrimeSegment 438173741 438304813).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 438173741 ≤ 438239277)
    (by decide : 438239277 ≤ 438304813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438173741 438304813).card = 462 := join_1_0

end S208C15
end Sude.GeneratedTwinScan
