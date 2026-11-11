import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19274)) 371458093 371490861 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371458093 371490861).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19274 371458093 371490861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19274)) 371490861 371523629 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371490861 371523629).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19274 371490861 371523629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19275)) 371523629 371556397 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371523629 371556397).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19275 371523629 371556397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19276)) 371556397 371589165 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371556397 371589165).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19276 371556397 371589165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371458093 371523629).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 371458093 ≤ 371490861)
    (by decide : 371490861 ≤ 371523629) block0 block1

theorem join_0_1 : (twinPrimeSegment 371523629 371589165).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 371523629 ≤ 371556397)
    (by decide : 371556397 ≤ 371589165) block2 block3

theorem join_1_0 : (twinPrimeSegment 371458093 371589165).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 371458093 ≤ 371523629)
    (by decide : 371523629 ≤ 371589165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371458093 371589165).card = 406 := join_1_0

end S177C02
end Sude.GeneratedTwinScan
