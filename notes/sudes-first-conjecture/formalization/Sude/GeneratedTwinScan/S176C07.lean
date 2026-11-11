import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19236)) 370016301 370049069 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 370016301 370049069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19236 370016301 370049069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19237)) 370049069 370081837 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 370049069 370081837).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19237 370049069 370081837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19238)) 370081837 370114605 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 370081837 370114605).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19238 370081837 370114605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19239)) 370114605 370147373 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 370114605 370147373).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19239 370114605 370147373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 370016301 370081837).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 370016301 ≤ 370049069)
    (by decide : 370049069 ≤ 370081837) block0 block1

theorem join_0_1 : (twinPrimeSegment 370081837 370147373).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 370081837 ≤ 370114605)
    (by decide : 370114605 ≤ 370147373) block2 block3

theorem join_1_0 : (twinPrimeSegment 370016301 370147373).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 370016301 ≤ 370081837)
    (by decide : 370081837 ≤ 370147373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 370016301 370147373).card = 441 := join_1_0

end S176C07
end Sude.GeneratedTwinScan
