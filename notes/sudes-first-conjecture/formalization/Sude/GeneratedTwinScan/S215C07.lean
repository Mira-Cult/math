import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21256)) 451805229 451837997 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 451805229 451837997).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21256 451805229 451837997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21257)) 451837997 451870765 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 451837997 451870765).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21257 451837997 451870765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21258)) 451870765 451903533 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 451870765 451903533).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21258 451870765 451903533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21258)) 451903533 451936301 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 451903533 451936301).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21258 451903533 451936301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 451805229 451870765).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 451805229 ≤ 451837997)
    (by decide : 451837997 ≤ 451870765) block0 block1

theorem join_0_1 : (twinPrimeSegment 451870765 451936301).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 451870765 ≤ 451903533)
    (by decide : 451903533 ≤ 451936301) block2 block3

theorem join_1_0 : (twinPrimeSegment 451805229 451936301).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 451805229 ≤ 451870765)
    (by decide : 451870765 ≤ 451936301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 451805229 451936301).card = 423 := join_1_0

end S215C07
end Sude.GeneratedTwinScan
