import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22450)) 503971885 504004653 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503971885 504004653).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22450 503971885 504004653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22450)) 504004653 504037421 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504004653 504037421).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22450 504004653 504037421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22451)) 504037421 504070189 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504037421 504070189).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22451 504037421 504070189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22452)) 504070189 504102957 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504070189 504102957).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22452 504070189 504102957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503971885 504037421).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 503971885 ≤ 504004653)
    (by decide : 504004653 ≤ 504037421) block0 block1

theorem join_0_1 : (twinPrimeSegment 504037421 504102957).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 504037421 ≤ 504070189)
    (by decide : 504070189 ≤ 504102957) block2 block3

theorem join_1_0 : (twinPrimeSegment 503971885 504102957).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 503971885 ≤ 504037421)
    (by decide : 504037421 ≤ 504102957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503971885 504102957).card = 450 := join_1_0

end S240C05
end Sude.GeneratedTwinScan
