import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18732)) 350879789 350912557 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 350879789 350912557).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18732 350879789 350912557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18733)) 350912557 350945325 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 350912557 350945325).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18733 350912557 350945325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18734)) 350945325 350978093 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 350945325 350978093).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18734 350945325 350978093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18735)) 350978093 351010861 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 350978093 351010861).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18735 350978093 351010861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 350879789 350945325).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 350879789 ≤ 350912557)
    (by decide : 350912557 ≤ 350945325) block0 block1

theorem join_0_1 : (twinPrimeSegment 350945325 351010861).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 350945325 ≤ 350978093)
    (by decide : 350978093 ≤ 351010861) block2 block3

theorem join_1_0 : (twinPrimeSegment 350879789 351010861).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 350879789 ≤ 350945325)
    (by decide : 350945325 ≤ 351010861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 350879789 351010861).card = 437 := join_1_0

end S167C05
end Sude.GeneratedTwinScan
