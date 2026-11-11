import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20011)) 400425005 400457773 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 400425005 400457773).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20011 400425005 400457773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20012)) 400457773 400490541 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 400457773 400490541).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20012 400457773 400490541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20013)) 400490541 400523309 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 400490541 400523309).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20013 400490541 400523309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20013)) 400523309 400556077 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 400523309 400556077).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20013 400523309 400556077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 400425005 400490541).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 400425005 ≤ 400457773)
    (by decide : 400457773 ≤ 400490541) block0 block1

theorem join_0_1 : (twinPrimeSegment 400490541 400556077).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 400490541 ≤ 400523309)
    (by decide : 400523309 ≤ 400556077) block2 block3

theorem join_1_0 : (twinPrimeSegment 400425005 400556077).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 400425005 ≤ 400490541)
    (by decide : 400490541 ≤ 400556077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 400425005 400556077).card = 439 := join_1_0

end S190C15
end Sude.GeneratedTwinScan
