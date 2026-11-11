import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22863)) 522715181 522747949 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522715181 522747949).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22863 522715181 522747949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22864)) 522747949 522780717 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 522747949 522780717).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22864 522747949 522780717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22865)) 522780717 522813485 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 522780717 522813485).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22865 522780717 522813485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22865)) 522813485 522846253 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522813485 522846253).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22865 522813485 522846253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522715181 522780717).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 522715181 ≤ 522747949)
    (by decide : 522747949 ≤ 522780717) block0 block1

theorem join_0_1 : (twinPrimeSegment 522780717 522846253).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 522780717 ≤ 522813485)
    (by decide : 522813485 ≤ 522846253) block2 block3

theorem join_1_0 : (twinPrimeSegment 522715181 522846253).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 522715181 ≤ 522780717)
    (by decide : 522780717 ≤ 522846253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522715181 522846253).card = 425 := join_1_0

end S249C04
end Sude.GeneratedTwinScan
