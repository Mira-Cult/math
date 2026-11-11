import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15711)) 246808621 246841389 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246808621 246841389).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15711 246808621 246841389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15712)) 246841389 246874157 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246841389 246874157).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15712 246841389 246874157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15713)) 246874157 246906925 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246874157 246906925).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15713 246874157 246906925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15714)) 246906925 246939693 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246906925 246939693).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15714 246906925 246939693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246808621 246874157).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 246808621 ≤ 246841389)
    (by decide : 246841389 ≤ 246874157) block0 block1

theorem join_0_1 : (twinPrimeSegment 246874157 246939693).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 246874157 ≤ 246906925)
    (by decide : 246906925 ≤ 246939693) block2 block3

theorem join_1_0 : (twinPrimeSegment 246808621 246939693).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 246808621 ≤ 246874157)
    (by decide : 246874157 ≤ 246939693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246808621 246939693).card = 450 := join_1_0

end S117C11
end Sude.GeneratedTwinScan
