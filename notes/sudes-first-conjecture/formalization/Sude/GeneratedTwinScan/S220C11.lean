import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21513)) 462815277 462848045 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462815277 462848045).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21513 462815277 462848045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21514)) 462848045 462880813 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462848045 462880813).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21514 462848045 462880813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21515)) 462880813 462913581 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462880813 462913581).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21515 462880813 462913581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21516)) 462913581 462946349 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462913581 462946349).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21516 462913581 462946349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462815277 462880813).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 462815277 ≤ 462848045)
    (by decide : 462848045 ≤ 462880813) block0 block1

theorem join_0_1 : (twinPrimeSegment 462880813 462946349).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 462880813 ≤ 462913581)
    (by decide : 462913581 ≤ 462946349) block2 block3

theorem join_1_0 : (twinPrimeSegment 462815277 462946349).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 462815277 ≤ 462880813)
    (by decide : 462880813 ≤ 462946349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462815277 462946349).card = 426 := join_1_0

end S220C11
end Sude.GeneratedTwinScan
