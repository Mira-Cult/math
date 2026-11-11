import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19714)) 388628525 388661293 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 388628525 388661293).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19714 388628525 388661293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19715)) 388661293 388694061 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388661293 388694061).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19715 388661293 388694061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19716)) 388694061 388726829 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388694061 388726829).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19716 388694061 388726829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19716)) 388726829 388759597 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388726829 388759597).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19716 388726829 388759597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 388628525 388694061).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 388628525 ≤ 388661293)
    (by decide : 388661293 ≤ 388694061) block0 block1

theorem join_0_1 : (twinPrimeSegment 388694061 388759597).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 388694061 ≤ 388726829)
    (by decide : 388726829 ≤ 388759597) block2 block3

theorem join_1_0 : (twinPrimeSegment 388628525 388759597).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 388628525 ≤ 388694061)
    (by decide : 388694061 ≤ 388759597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 388628525 388759597).card = 453 := join_1_0

end S185C05
end Sude.GeneratedTwinScan
