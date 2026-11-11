import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14536)) 211288109 211320877 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211288109 211320877).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14536 211288109 211320877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14538)) 211320877 211353645 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211320877 211353645).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14538 211320877 211353645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14539)) 211353645 211386413 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 211353645 211386413).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14539 211353645 211386413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14540)) 211386413 211419181 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 211386413 211419181).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14540 211386413 211419181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211288109 211353645).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 211288109 ≤ 211320877)
    (by decide : 211320877 ≤ 211353645) block0 block1

theorem join_0_1 : (twinPrimeSegment 211353645 211419181).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 211353645 ≤ 211386413)
    (by decide : 211386413 ≤ 211419181) block2 block3

theorem join_1_0 : (twinPrimeSegment 211288109 211419181).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 211288109 ≤ 211353645)
    (by decide : 211353645 ≤ 211419181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211288109 211419181).card = 493 := join_1_0

end S100C12
end Sude.GeneratedTwinScan
