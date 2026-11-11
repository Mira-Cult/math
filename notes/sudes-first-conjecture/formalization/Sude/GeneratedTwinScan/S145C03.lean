import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17450)) 304480301 304513069 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 304480301 304513069).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17450 304480301 304513069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17451)) 304513069 304545837 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 304513069 304545837).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17451 304513069 304545837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17452)) 304545837 304578605 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304545837 304578605).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17452 304545837 304578605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17453)) 304578605 304611373 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304578605 304611373).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17453 304578605 304611373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 304480301 304545837).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 304480301 ≤ 304513069)
    (by decide : 304513069 ≤ 304545837) block0 block1

theorem join_0_1 : (twinPrimeSegment 304545837 304611373).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 304545837 ≤ 304578605)
    (by decide : 304578605 ≤ 304611373) block2 block3

theorem join_1_0 : (twinPrimeSegment 304480301 304611373).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 304480301 ≤ 304545837)
    (by decide : 304545837 ≤ 304611373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 304480301 304611373).card = 492 := join_1_0

end S145C03
end Sude.GeneratedTwinScan
