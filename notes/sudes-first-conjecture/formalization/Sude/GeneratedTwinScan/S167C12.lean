import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18757)) 351797293 351830061 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351797293 351830061).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18757 351797293 351830061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18758)) 351830061 351862829 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351830061 351862829).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18758 351830061 351862829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18758)) 351862829 351895597 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351862829 351895597).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18758 351862829 351895597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18759)) 351895597 351928365 = 81 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 351895597 351928365).card = 81 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18759 351895597 351928365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351797293 351862829).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 351797293 ≤ 351830061)
    (by decide : 351830061 ≤ 351862829) block0 block1

theorem join_0_1 : (twinPrimeSegment 351862829 351928365).card = 181 := by
  simpa using combineTwinPrimeSegments (by decide : 351862829 ≤ 351895597)
    (by decide : 351895597 ≤ 351928365) block2 block3

theorem join_1_0 : (twinPrimeSegment 351797293 351928365).card = 383 := by
  simpa using combineTwinPrimeSegments (by decide : 351797293 ≤ 351862829)
    (by decide : 351862829 ≤ 351928365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351797293 351928365).card = 383 := join_1_0

end S167C12
end Sude.GeneratedTwinScan
