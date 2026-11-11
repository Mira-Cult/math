import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17931)) 321519661 321552429 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 321519661 321552429).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17931 321519661 321552429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17932)) 321552429 321585197 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321552429 321585197).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17932 321552429 321585197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17933)) 321585197 321617965 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321585197 321617965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17933 321585197 321617965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17934)) 321617965 321650733 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 321617965 321650733).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17934 321617965 321650733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 321519661 321585197).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 321519661 ≤ 321552429)
    (by decide : 321552429 ≤ 321585197) block0 block1

theorem join_0_1 : (twinPrimeSegment 321585197 321650733).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 321585197 ≤ 321617965)
    (by decide : 321617965 ≤ 321650733) block2 block3

theorem join_1_0 : (twinPrimeSegment 321519661 321650733).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 321519661 ≤ 321585197)
    (by decide : 321585197 ≤ 321650733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 321519661 321650733).card = 455 := join_1_0

end S153C05
end Sude.GeneratedTwinScan
