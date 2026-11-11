import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17397)) 302645293 302678061 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302645293 302678061).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17397 302645293 302678061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17398)) 302678061 302710829 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302678061 302710829).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17398 302678061 302710829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17399)) 302710829 302743597 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302710829 302743597).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17399 302710829 302743597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17400)) 302743597 302776365 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302743597 302776365).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17400 302743597 302776365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302645293 302710829).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 302645293 ≤ 302678061)
    (by decide : 302678061 ≤ 302710829) block0 block1

theorem join_0_1 : (twinPrimeSegment 302710829 302776365).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 302710829 ≤ 302743597)
    (by decide : 302743597 ≤ 302776365) block2 block3

theorem join_1_0 : (twinPrimeSegment 302645293 302776365).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 302645293 ≤ 302710829)
    (by decide : 302710829 ≤ 302776365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302645293 302776365).card = 428 := join_1_0

end S144C05
end Sude.GeneratedTwinScan
