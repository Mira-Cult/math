import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22525)) 507379757 507412525 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507379757 507412525).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22525 507379757 507412525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22526)) 507412525 507445293 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507412525 507445293).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22526 507412525 507445293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22527)) 507445293 507478061 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507445293 507478061).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22527 507445293 507478061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22528)) 507478061 507510829 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507478061 507510829).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22528 507478061 507510829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507379757 507445293).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 507379757 ≤ 507412525)
    (by decide : 507412525 ≤ 507445293) block0 block1

theorem join_0_1 : (twinPrimeSegment 507445293 507510829).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 507445293 ≤ 507478061)
    (by decide : 507478061 ≤ 507510829) block2 block3

theorem join_1_0 : (twinPrimeSegment 507379757 507510829).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 507379757 ≤ 507445293)
    (by decide : 507445293 ≤ 507510829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507379757 507510829).card = 427 := join_1_0

end S241C15
end Sude.GeneratedTwinScan
