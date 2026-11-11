import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17124)) 293208109 293240877 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293208109 293240877).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17124 293208109 293240877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17125)) 293240877 293273645 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 293240877 293273645).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17125 293240877 293273645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17126)) 293273645 293306413 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293273645 293306413).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17126 293273645 293306413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17127)) 293306413 293339181 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293306413 293339181).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17127 293306413 293339181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293208109 293273645).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 293208109 ≤ 293240877)
    (by decide : 293240877 ≤ 293273645) block0 block1

theorem join_0_1 : (twinPrimeSegment 293273645 293339181).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 293273645 ≤ 293306413)
    (by decide : 293306413 ≤ 293339181) block2 block3

theorem join_1_0 : (twinPrimeSegment 293208109 293339181).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 293208109 ≤ 293273645)
    (by decide : 293273645 ≤ 293339181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293208109 293339181).card = 468 := join_1_0

end S139C13
end Sude.GeneratedTwinScan
