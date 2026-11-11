import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17457)) 304742445 304775213 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 304742445 304775213).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17457 304742445 304775213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17458)) 304775213 304807981 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 304775213 304807981).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17458 304775213 304807981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17459)) 304807981 304840749 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304807981 304840749).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17459 304807981 304840749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17460)) 304840749 304873517 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304840749 304873517).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17460 304840749 304873517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 304742445 304807981).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 304742445 ≤ 304775213)
    (by decide : 304775213 ≤ 304807981) block0 block1

theorem join_0_1 : (twinPrimeSegment 304807981 304873517).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 304807981 ≤ 304840749)
    (by decide : 304840749 ≤ 304873517) block2 block3

theorem join_1_0 : (twinPrimeSegment 304742445 304873517).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 304742445 ≤ 304807981)
    (by decide : 304807981 ≤ 304873517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 304742445 304873517).card = 454 := join_1_0

end S145C05
end Sude.GeneratedTwinScan
