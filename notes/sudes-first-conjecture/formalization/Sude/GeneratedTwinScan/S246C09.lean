import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22740)) 517079085 517111853 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 517079085 517111853).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22740 517079085 517111853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22740)) 517111853 517144621 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 517111853 517144621).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22740 517111853 517144621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22741)) 517144621 517177389 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 517144621 517177389).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22741 517144621 517177389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22742)) 517177389 517210157 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 517177389 517210157).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22742 517177389 517210157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 517079085 517144621).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 517079085 ≤ 517111853)
    (by decide : 517111853 ≤ 517144621) block0 block1

theorem join_0_1 : (twinPrimeSegment 517144621 517210157).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 517144621 ≤ 517177389)
    (by decide : 517177389 ≤ 517210157) block2 block3

theorem join_1_0 : (twinPrimeSegment 517079085 517210157).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 517079085 ≤ 517144621)
    (by decide : 517144621 ≤ 517210157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 517079085 517210157).card = 413 := join_1_0

end S246C09
end Sude.GeneratedTwinScan
