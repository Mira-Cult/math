import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17993)) 323747885 323780653 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323747885 323780653).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17993 323747885 323780653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17994)) 323780653 323813421 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323780653 323813421).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17994 323780653 323813421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17995)) 323813421 323846189 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323813421 323846189).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17995 323813421 323846189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17996)) 323846189 323878957 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323846189 323878957).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17996 323846189 323878957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323747885 323813421).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 323747885 ≤ 323780653)
    (by decide : 323780653 ≤ 323813421) block0 block1

theorem join_0_1 : (twinPrimeSegment 323813421 323878957).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 323813421 ≤ 323846189)
    (by decide : 323846189 ≤ 323878957) block2 block3

theorem join_1_0 : (twinPrimeSegment 323747885 323878957).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 323747885 ≤ 323813421)
    (by decide : 323813421 ≤ 323878957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323747885 323878957).card = 428 := join_1_0

end S154C06
end Sude.GeneratedTwinScan
