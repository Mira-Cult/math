import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21452)) 460193837 460226605 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460193837 460226605).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21452 460193837 460226605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21453)) 460226605 460259373 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460226605 460259373).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21453 460226605 460259373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21454)) 460259373 460292141 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460259373 460292141).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21454 460259373 460292141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21455)) 460292141 460324909 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460292141 460324909).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21455 460292141 460324909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460193837 460259373).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 460193837 ≤ 460226605)
    (by decide : 460226605 ≤ 460259373) block0 block1

theorem join_0_1 : (twinPrimeSegment 460259373 460324909).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 460259373 ≤ 460292141)
    (by decide : 460292141 ≤ 460324909) block2 block3

theorem join_1_0 : (twinPrimeSegment 460193837 460324909).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 460193837 ≤ 460259373)
    (by decide : 460259373 ≤ 460324909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460193837 460324909).card = 416 := join_1_0

end S219C07
end Sude.GeneratedTwinScan
