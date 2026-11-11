import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22659)) 513409069 513441837 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513409069 513441837).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22659 513409069 513441837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22659)) 513441837 513474605 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513441837 513474605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22659 513441837 513474605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22660)) 513474605 513507373 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513474605 513507373).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22660 513474605 513507373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22661)) 513507373 513540141 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513507373 513540141).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22661 513507373 513540141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513409069 513474605).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 513409069 ≤ 513441837)
    (by decide : 513441837 ≤ 513474605) block0 block1

theorem join_0_1 : (twinPrimeSegment 513474605 513540141).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 513474605 ≤ 513507373)
    (by decide : 513507373 ≤ 513540141) block2 block3

theorem join_1_0 : (twinPrimeSegment 513409069 513540141).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 513409069 ≤ 513474605)
    (by decide : 513474605 ≤ 513540141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513409069 513540141).card = 468 := join_1_0

end S244C13
end Sude.GeneratedTwinScan
