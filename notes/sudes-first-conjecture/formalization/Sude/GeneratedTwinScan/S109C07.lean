import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15150)) 229507117 229539885 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229507117 229539885).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15150 229507117 229539885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15151)) 229539885 229572653 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229539885 229572653).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15151 229539885 229572653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15152)) 229572653 229605421 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229572653 229605421).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15152 229572653 229605421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15153)) 229605421 229638189 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229605421 229638189).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15153 229605421 229638189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229507117 229572653).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 229507117 ≤ 229539885)
    (by decide : 229539885 ≤ 229572653) block0 block1

theorem join_0_1 : (twinPrimeSegment 229572653 229638189).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 229572653 ≤ 229605421)
    (by decide : 229605421 ≤ 229638189) block2 block3

theorem join_1_0 : (twinPrimeSegment 229507117 229638189).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 229507117 ≤ 229572653)
    (by decide : 229572653 ≤ 229638189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229507117 229638189).card = 464 := join_1_0

end S109C07
end Sude.GeneratedTwinScan
