import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15433)) 238157869 238190637 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238157869 238190637).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15433 238157869 238190637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15434)) 238190637 238223405 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238190637 238223405).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15434 238190637 238223405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15435)) 238223405 238256173 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238223405 238256173).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15435 238223405 238256173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15436)) 238256173 238288941 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238256173 238288941).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15436 238256173 238288941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238157869 238223405).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 238157869 ≤ 238190637)
    (by decide : 238190637 ≤ 238223405) block0 block1

theorem join_0_1 : (twinPrimeSegment 238223405 238288941).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 238223405 ≤ 238256173)
    (by decide : 238256173 ≤ 238288941) block2 block3

theorem join_1_0 : (twinPrimeSegment 238157869 238288941).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 238157869 ≤ 238223405)
    (by decide : 238223405 ≤ 238288941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238157869 238288941).card = 485 := join_1_0

end S113C09
end Sude.GeneratedTwinScan
