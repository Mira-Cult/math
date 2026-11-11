import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15395)) 236978221 237010989 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236978221 237010989).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15395 236978221 237010989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15396)) 237010989 237043757 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237010989 237043757).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15396 237010989 237043757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15397)) 237043757 237076525 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237043757 237076525).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15397 237043757 237076525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15398)) 237076525 237109293 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237076525 237109293).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15398 237076525 237109293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236978221 237043757).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 236978221 ≤ 237010989)
    (by decide : 237010989 ≤ 237043757) block0 block1

theorem join_0_1 : (twinPrimeSegment 237043757 237109293).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 237043757 ≤ 237076525)
    (by decide : 237076525 ≤ 237109293) block2 block3

theorem join_1_0 : (twinPrimeSegment 236978221 237109293).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 236978221 ≤ 237043757)
    (by decide : 237043757 ≤ 237109293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236978221 237109293).card = 496 := join_1_0

end S113C00
end Sude.GeneratedTwinScan
