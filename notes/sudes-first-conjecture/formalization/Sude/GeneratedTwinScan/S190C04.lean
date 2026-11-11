import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19975)) 398983213 399015981 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 398983213 399015981).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19975 398983213 399015981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19976)) 399015981 399048749 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399015981 399048749).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19976 399015981 399048749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19977)) 399048749 399081517 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399048749 399081517).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19977 399048749 399081517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19977)) 399081517 399114285 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399081517 399114285).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19977 399081517 399114285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 398983213 399048749).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 398983213 ≤ 399015981)
    (by decide : 399015981 ≤ 399048749) block0 block1

theorem join_0_1 : (twinPrimeSegment 399048749 399114285).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 399048749 ≤ 399081517)
    (by decide : 399081517 ≤ 399114285) block2 block3

theorem join_1_0 : (twinPrimeSegment 398983213 399114285).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 398983213 ≤ 399048749)
    (by decide : 399048749 ≤ 399114285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 398983213 399114285).card = 443 := join_1_0

end S190C04
end Sude.GeneratedTwinScan
