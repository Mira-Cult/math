import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13749)) 189005869 189038637 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 189005869 189038637).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13749 189005869 189038637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13750)) 189038637 189071405 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 189038637 189071405).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13750 189038637 189071405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13751)) 189071405 189104173 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 189071405 189104173).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13751 189071405 189104173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13752)) 189104173 189136941 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 189104173 189136941).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13752 189104173 189136941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 189005869 189071405).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 189005869 ≤ 189038637)
    (by decide : 189038637 ≤ 189071405) block0 block1

theorem join_0_1 : (twinPrimeSegment 189071405 189136941).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 189071405 ≤ 189104173)
    (by decide : 189104173 ≤ 189136941) block2 block3

theorem join_1_0 : (twinPrimeSegment 189005869 189136941).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 189005869 ≤ 189071405)
    (by decide : 189071405 ≤ 189136941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 189005869 189136941).card = 477 := join_1_0

end S090C02
end Sude.GeneratedTwinScan
