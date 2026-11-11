import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22519)) 507117613 507150381 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507117613 507150381).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22519 507117613 507150381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22520)) 507150381 507183149 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507150381 507183149).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22520 507150381 507183149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22521)) 507183149 507215917 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507183149 507215917).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22521 507183149 507215917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22522)) 507215917 507248685 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507215917 507248685).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22522 507215917 507248685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507117613 507183149).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 507117613 ≤ 507150381)
    (by decide : 507150381 ≤ 507183149) block0 block1

theorem join_0_1 : (twinPrimeSegment 507183149 507248685).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 507183149 ≤ 507215917)
    (by decide : 507215917 ≤ 507248685) block2 block3

theorem join_1_0 : (twinPrimeSegment 507117613 507248685).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 507117613 ≤ 507183149)
    (by decide : 507183149 ≤ 507248685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507117613 507248685).card = 431 := join_1_0

end S241C13
end Sude.GeneratedTwinScan
