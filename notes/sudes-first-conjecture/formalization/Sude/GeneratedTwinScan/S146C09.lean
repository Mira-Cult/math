import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17532)) 307363885 307396653 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 307363885 307396653).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17532 307363885 307396653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17533)) 307396653 307429421 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 307396653 307429421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17533 307396653 307429421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17534)) 307429421 307462189 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 307429421 307462189).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17534 307429421 307462189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17535)) 307462189 307494957 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 307462189 307494957).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17535 307462189 307494957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 307363885 307429421).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 307363885 ≤ 307396653)
    (by decide : 307396653 ≤ 307429421) block0 block1

theorem join_0_1 : (twinPrimeSegment 307429421 307494957).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 307429421 ≤ 307462189)
    (by decide : 307462189 ≤ 307494957) block2 block3

theorem join_1_0 : (twinPrimeSegment 307363885 307494957).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 307363885 ≤ 307429421)
    (by decide : 307429421 ≤ 307494957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 307363885 307494957).card = 454 := join_1_0

end S146C09
end Sude.GeneratedTwinScan
