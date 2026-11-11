import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13772)) 189661229 189693997 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 189661229 189693997).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13772 189661229 189693997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13774)) 189693997 189726765 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 189693997 189726765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13774 189693997 189726765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13775)) 189726765 189759533 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 189726765 189759533).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13775 189726765 189759533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13776)) 189759533 189792301 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 189759533 189792301).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13776 189759533 189792301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 189661229 189726765).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 189661229 ≤ 189693997)
    (by decide : 189693997 ≤ 189726765) block0 block1

theorem join_0_1 : (twinPrimeSegment 189726765 189792301).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 189726765 ≤ 189759533)
    (by decide : 189759533 ≤ 189792301) block2 block3

theorem join_1_0 : (twinPrimeSegment 189661229 189792301).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 189661229 ≤ 189726765)
    (by decide : 189726765 ≤ 189792301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 189661229 189792301).card = 489 := join_1_0

end S090C07
end Sude.GeneratedTwinScan
