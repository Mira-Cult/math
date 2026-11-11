import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21086)) 444596269 444629037 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444596269 444629037).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21086 444596269 444629037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21087)) 444629037 444661805 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 444629037 444661805).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21087 444629037 444661805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21087)) 444661805 444694573 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 444661805 444694573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21087 444661805 444694573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21088)) 444694573 444727341 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 444694573 444727341).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21088 444694573 444727341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444596269 444661805).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 444629037)
    (by decide : 444629037 ≤ 444661805) block0 block1

theorem join_0_1 : (twinPrimeSegment 444661805 444727341).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 444661805 ≤ 444694573)
    (by decide : 444694573 ≤ 444727341) block2 block3

theorem join_1_0 : (twinPrimeSegment 444596269 444727341).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 444661805)
    (by decide : 444661805 ≤ 444727341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444596269 444727341).card = 450 := join_1_0

end S212C00
end Sude.GeneratedTwinScan
