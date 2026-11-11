import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21744)) 472776749 472809517 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472776749 472809517).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21744 472776749 472809517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21744)) 472809517 472842285 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472809517 472842285).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21744 472809517 472842285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21745)) 472842285 472875053 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472842285 472875053).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21745 472842285 472875053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21746)) 472875053 472907821 = 83 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472875053 472907821).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21746 472875053 472907821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472776749 472842285).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 472776749 ≤ 472809517)
    (by decide : 472809517 ≤ 472842285) block0 block1

theorem join_0_1 : (twinPrimeSegment 472842285 472907821).card = 185 := by
  simpa using combineTwinPrimeSegments (by decide : 472842285 ≤ 472875053)
    (by decide : 472875053 ≤ 472907821) block2 block3

theorem join_1_0 : (twinPrimeSegment 472776749 472907821).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 472776749 ≤ 472842285)
    (by decide : 472842285 ≤ 472907821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472776749 472907821).card = 406 := join_1_0

end S225C07
end Sude.GeneratedTwinScan
