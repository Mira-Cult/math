import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13455)) 181010477 181043245 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181010477 181043245).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13455 181010477 181043245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13456)) 181043245 181076013 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181043245 181076013).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13456 181043245 181076013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13457)) 181076013 181108781 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181076013 181108781).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13457 181076013 181108781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13458)) 181108781 181141549 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181108781 181141549).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13458 181108781 181141549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181010477 181076013).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 181010477 ≤ 181043245)
    (by decide : 181043245 ≤ 181076013) block0 block1

theorem join_0_1 : (twinPrimeSegment 181076013 181141549).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 181076013 ≤ 181108781)
    (by decide : 181108781 ≤ 181141549) block2 block3

theorem join_1_0 : (twinPrimeSegment 181010477 181141549).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 181010477 ≤ 181076013)
    (by decide : 181076013 ≤ 181141549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181010477 181141549).card = 476 := join_1_0

end S086C05
end Sude.GeneratedTwinScan
