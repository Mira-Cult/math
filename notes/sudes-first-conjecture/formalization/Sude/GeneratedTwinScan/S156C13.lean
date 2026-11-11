import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18135)) 328859693 328892461 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 328859693 328892461).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18135 328859693 328892461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18136)) 328892461 328925229 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 328892461 328925229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18136 328892461 328925229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18137)) 328925229 328957997 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 328925229 328957997).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18137 328925229 328957997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18138)) 328957997 328990765 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 328957997 328990765).card = 144 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18138 328957997 328990765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 328859693 328925229).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 328859693 ≤ 328892461)
    (by decide : 328892461 ≤ 328925229) block0 block1

theorem join_0_1 : (twinPrimeSegment 328925229 328990765).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 328925229 ≤ 328957997)
    (by decide : 328957997 ≤ 328990765) block2 block3

theorem join_1_0 : (twinPrimeSegment 328859693 328990765).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 328859693 ≤ 328925229)
    (by decide : 328925229 ≤ 328990765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 328859693 328990765).card = 487 := join_1_0

end S156C13
end Sude.GeneratedTwinScan
