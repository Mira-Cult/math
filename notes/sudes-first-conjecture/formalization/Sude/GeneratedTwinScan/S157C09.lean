import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18178)) 330432557 330465325 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 330432557 330465325).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18178 330432557 330465325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18179)) 330465325 330498093 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 330465325 330498093).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18179 330465325 330498093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18180)) 330498093 330530861 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 330498093 330530861).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18180 330498093 330530861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18181)) 330530861 330563629 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330530861 330563629).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18181 330530861 330563629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 330432557 330498093).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 330432557 ≤ 330465325)
    (by decide : 330465325 ≤ 330498093) block0 block1

theorem join_0_1 : (twinPrimeSegment 330498093 330563629).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 330498093 ≤ 330530861)
    (by decide : 330530861 ≤ 330563629) block2 block3

theorem join_1_0 : (twinPrimeSegment 330432557 330563629).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 330432557 ≤ 330498093)
    (by decide : 330498093 ≤ 330563629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 330432557 330563629).card = 458 := join_1_0

end S157C09
end Sude.GeneratedTwinScan
