import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13615)) 185335853 185368621 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185335853 185368621).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13615 185335853 185368621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13616)) 185368621 185401389 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185368621 185401389).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13616 185368621 185401389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13617)) 185401389 185434157 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185401389 185434157).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13617 185401389 185434157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13618)) 185434157 185466925 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185434157 185466925).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13618 185434157 185466925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185335853 185401389).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 185335853 ≤ 185368621)
    (by decide : 185368621 ≤ 185401389) block0 block1

theorem join_0_1 : (twinPrimeSegment 185401389 185466925).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 185401389 ≤ 185434157)
    (by decide : 185434157 ≤ 185466925) block2 block3

theorem join_1_0 : (twinPrimeSegment 185335853 185466925).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 185335853 ≤ 185401389)
    (by decide : 185401389 ≤ 185466925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185335853 185466925).card = 479 := join_1_0

end S088C06
end Sude.GeneratedTwinScan
