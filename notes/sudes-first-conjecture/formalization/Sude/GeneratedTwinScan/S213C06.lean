import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21154)) 447479853 447512621 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 447479853 447512621).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21154 447479853 447512621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21155)) 447512621 447545389 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 447512621 447545389).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21155 447512621 447545389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21156)) 447545389 447578157 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447545389 447578157).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21156 447545389 447578157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21156)) 447578157 447610925 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447578157 447610925).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21156 447578157 447610925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 447479853 447545389).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 447479853 ≤ 447512621)
    (by decide : 447512621 ≤ 447545389) block0 block1

theorem join_0_1 : (twinPrimeSegment 447545389 447610925).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 447545389 ≤ 447578157)
    (by decide : 447578157 ≤ 447610925) block2 block3

theorem join_1_0 : (twinPrimeSegment 447479853 447610925).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 447479853 ≤ 447545389)
    (by decide : 447545389 ≤ 447610925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 447479853 447610925).card = 432 := join_1_0

end S213C06
end Sude.GeneratedTwinScan
