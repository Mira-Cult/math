import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16795)) 282066989 282099757 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 282066989 282099757).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16795 282066989 282099757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16796)) 282099757 282132525 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 282099757 282132525).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16796 282099757 282132525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16797)) 282132525 282165293 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 282132525 282165293).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16797 282132525 282165293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16798)) 282165293 282198061 = 91 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 282165293 282198061).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16798 282165293 282198061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 282066989 282132525).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 282066989 ≤ 282099757)
    (by decide : 282099757 ≤ 282132525) block0 block1

theorem join_0_1 : (twinPrimeSegment 282132525 282198061).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 282132525 ≤ 282165293)
    (by decide : 282165293 ≤ 282198061) block2 block3

theorem join_1_0 : (twinPrimeSegment 282066989 282198061).card = 408 := by
  simpa using combineTwinPrimeSegments (by decide : 282066989 ≤ 282132525)
    (by decide : 282132525 ≤ 282198061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 282066989 282198061).card = 408 := join_1_0

end S134C08
end Sude.GeneratedTwinScan
