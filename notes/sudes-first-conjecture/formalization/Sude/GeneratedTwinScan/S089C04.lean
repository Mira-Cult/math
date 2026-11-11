import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13682)) 187170861 187203629 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187170861 187203629).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13682 187170861 187203629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13683)) 187203629 187236397 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187203629 187236397).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13683 187203629 187236397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13684)) 187236397 187269165 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 187236397 187269165).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13684 187236397 187269165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13685)) 187269165 187301933 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187269165 187301933).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13685 187269165 187301933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187170861 187236397).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 187170861 ≤ 187203629)
    (by decide : 187203629 ≤ 187236397) block0 block1

theorem join_0_1 : (twinPrimeSegment 187236397 187301933).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 187236397 ≤ 187269165)
    (by decide : 187269165 ≤ 187301933) block2 block3

theorem join_1_0 : (twinPrimeSegment 187170861 187301933).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 187170861 ≤ 187236397)
    (by decide : 187236397 ≤ 187301933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187170861 187301933).card = 480 := join_1_0

end S089C04
end Sude.GeneratedTwinScan
