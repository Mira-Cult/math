import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15748)) 247988269 248021037 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247988269 248021037).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15748 247988269 248021037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15749)) 248021037 248053805 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248021037 248053805).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15749 248021037 248053805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15750)) 248053805 248086573 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248053805 248086573).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15750 248053805 248086573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15751)) 248086573 248119341 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248086573 248119341).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15751 248086573 248119341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247988269 248053805).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 247988269 ≤ 248021037)
    (by decide : 248021037 ≤ 248053805) block0 block1

theorem join_0_1 : (twinPrimeSegment 248053805 248119341).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 248053805 ≤ 248086573)
    (by decide : 248086573 ≤ 248119341) block2 block3

theorem join_1_0 : (twinPrimeSegment 247988269 248119341).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 247988269 ≤ 248053805)
    (by decide : 248053805 ≤ 248119341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247988269 248119341).card = 454 := join_1_0

end S118C04
end Sude.GeneratedTwinScan
