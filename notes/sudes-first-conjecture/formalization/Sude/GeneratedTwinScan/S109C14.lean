import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15180)) 230424621 230457389 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230424621 230457389).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15180 230424621 230457389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15181)) 230457389 230490157 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230457389 230490157).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15181 230457389 230490157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15182)) 230490157 230522925 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 230490157 230522925).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15182 230490157 230522925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15184)) 230522925 230555693 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 230522925 230555693).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15184 230522925 230555693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230424621 230490157).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 230424621 ≤ 230457389)
    (by decide : 230457389 ≤ 230490157) block0 block1

theorem join_0_1 : (twinPrimeSegment 230490157 230555693).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 230490157 ≤ 230522925)
    (by decide : 230522925 ≤ 230555693) block2 block3

theorem join_1_0 : (twinPrimeSegment 230424621 230555693).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 230424621 ≤ 230490157)
    (by decide : 230490157 ≤ 230555693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230424621 230555693).card = 462 := join_1_0

end S109C14
end Sude.GeneratedTwinScan
