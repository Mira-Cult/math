import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20067)) 402653229 402685997 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402653229 402685997).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20067 402653229 402685997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20067)) 402685997 402718765 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402685997 402718765).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20067 402685997 402718765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20068)) 402718765 402751533 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402718765 402751533).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20068 402718765 402751533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20069)) 402751533 402784301 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402751533 402784301).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20069 402751533 402784301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402653229 402718765).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 402685997)
    (by decide : 402685997 ≤ 402718765) block0 block1

theorem join_0_1 : (twinPrimeSegment 402718765 402784301).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 402718765 ≤ 402751533)
    (by decide : 402751533 ≤ 402784301) block2 block3

theorem join_1_0 : (twinPrimeSegment 402653229 402784301).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 402718765)
    (by decide : 402718765 ≤ 402784301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402653229 402784301).card = 418 := join_1_0

end S192C00
end Sude.GeneratedTwinScan
