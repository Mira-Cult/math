import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17611)) 310116397 310149165 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310116397 310149165).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17611 310116397 310149165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17611)) 310149165 310181933 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310149165 310181933).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17611 310149165 310181933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17612)) 310181933 310214701 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310181933 310214701).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17612 310181933 310214701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17613)) 310214701 310247469 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310214701 310247469).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17613 310214701 310247469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310116397 310181933).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 310116397 ≤ 310149165)
    (by decide : 310149165 ≤ 310181933) block0 block1

theorem join_0_1 : (twinPrimeSegment 310181933 310247469).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 310181933 ≤ 310214701)
    (by decide : 310214701 ≤ 310247469) block2 block3

theorem join_1_0 : (twinPrimeSegment 310116397 310247469).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 310116397 ≤ 310181933)
    (by decide : 310181933 ≤ 310247469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310116397 310247469).card = 467 := join_1_0

end S147C14
end Sude.GeneratedTwinScan
