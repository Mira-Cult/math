import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14263)) 203423789 203456557 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203423789 203456557).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14263 203423789 203456557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14264)) 203456557 203489325 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203456557 203489325).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14264 203456557 203489325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14266)) 203489325 203522093 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203489325 203522093).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14266 203489325 203522093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14267)) 203522093 203554861 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203522093 203554861).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14267 203522093 203554861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203423789 203489325).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 203423789 ≤ 203456557)
    (by decide : 203456557 ≤ 203489325) block0 block1

theorem join_0_1 : (twinPrimeSegment 203489325 203554861).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 203489325 ≤ 203522093)
    (by decide : 203522093 ≤ 203554861) block2 block3

theorem join_1_0 : (twinPrimeSegment 203423789 203554861).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 203423789 ≤ 203489325)
    (by decide : 203489325 ≤ 203554861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203423789 203554861).card = 467 := join_1_0

end S097C00
end Sude.GeneratedTwinScan
