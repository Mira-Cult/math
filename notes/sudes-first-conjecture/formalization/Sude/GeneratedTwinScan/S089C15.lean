import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13734)) 188612653 188645421 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188612653 188645421).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13734 188612653 188645421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13736)) 188645421 188678189 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188645421 188678189).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13736 188645421 188678189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13737)) 188678189 188710957 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188678189 188710957).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13737 188678189 188710957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13738)) 188710957 188743725 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188710957 188743725).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13738 188710957 188743725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188612653 188678189).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 188612653 ≤ 188645421)
    (by decide : 188645421 ≤ 188678189) block0 block1

theorem join_0_1 : (twinPrimeSegment 188678189 188743725).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 188678189 ≤ 188710957)
    (by decide : 188710957 ≤ 188743725) block2 block3

theorem join_1_0 : (twinPrimeSegment 188612653 188743725).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 188612653 ≤ 188678189)
    (by decide : 188678189 ≤ 188743725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188612653 188743725).card = 462 := join_1_0

end S089C15
end Sude.GeneratedTwinScan
