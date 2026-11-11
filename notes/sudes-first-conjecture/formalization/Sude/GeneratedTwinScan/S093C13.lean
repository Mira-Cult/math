import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14027)) 196739117 196771885 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 196739117 196771885).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14027 196739117 196771885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14028)) 196771885 196804653 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 196771885 196804653).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14028 196771885 196804653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14029)) 196804653 196837421 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196804653 196837421).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14029 196804653 196837421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14031)) 196837421 196870189 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196837421 196870189).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14031 196837421 196870189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 196739117 196804653).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 196739117 ≤ 196771885)
    (by decide : 196771885 ≤ 196804653) block0 block1

theorem join_0_1 : (twinPrimeSegment 196804653 196870189).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 196804653 ≤ 196837421)
    (by decide : 196837421 ≤ 196870189) block2 block3

theorem join_1_0 : (twinPrimeSegment 196739117 196870189).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 196739117 ≤ 196804653)
    (by decide : 196804653 ≤ 196870189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 196739117 196870189).card = 481 := join_1_0

end S093C13
end Sude.GeneratedTwinScan
