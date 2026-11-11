import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19770)) 390856749 390889517 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 390856749 390889517).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19770 390856749 390889517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19771)) 390889517 390922285 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 390889517 390922285).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19771 390889517 390922285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19772)) 390922285 390955053 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 390922285 390955053).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19772 390922285 390955053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19773)) 390955053 390987821 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 390955053 390987821).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19773 390955053 390987821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 390856749 390922285).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 390856749 ≤ 390889517)
    (by decide : 390889517 ≤ 390922285) block0 block1

theorem join_0_1 : (twinPrimeSegment 390922285 390987821).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 390922285 ≤ 390955053)
    (by decide : 390955053 ≤ 390987821) block2 block3

theorem join_1_0 : (twinPrimeSegment 390856749 390987821).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 390856749 ≤ 390922285)
    (by decide : 390922285 ≤ 390987821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 390856749 390987821).card = 442 := join_1_0

end S186C06
end Sude.GeneratedTwinScan
