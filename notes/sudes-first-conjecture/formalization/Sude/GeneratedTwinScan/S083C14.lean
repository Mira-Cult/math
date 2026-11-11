import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13263)) 175898669 175931437 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175898669 175931437).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13263 175898669 175931437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13265)) 175931437 175964205 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175931437 175964205).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13265 175931437 175964205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13266)) 175964205 175996973 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175964205 175996973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13266 175964205 175996973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13267)) 175996973 176029741 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175996973 176029741).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13267 175996973 176029741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175898669 175964205).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 175898669 ≤ 175931437)
    (by decide : 175931437 ≤ 175964205) block0 block1

theorem join_0_1 : (twinPrimeSegment 175964205 176029741).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 175964205 ≤ 175996973)
    (by decide : 175996973 ≤ 176029741) block2 block3

theorem join_1_0 : (twinPrimeSegment 175898669 176029741).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 175898669 ≤ 175964205)
    (by decide : 175964205 ≤ 176029741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175898669 176029741).card = 500 := join_1_0

end S083C14
end Sude.GeneratedTwinScan
