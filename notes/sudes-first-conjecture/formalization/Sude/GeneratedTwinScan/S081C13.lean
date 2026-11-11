import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13099)) 171573293 171606061 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171573293 171606061).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13099 171573293 171606061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13101)) 171606061 171638829 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171606061 171638829).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13101 171606061 171638829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13102)) 171638829 171671597 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 171638829 171671597).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13102 171638829 171671597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13103)) 171671597 171704365 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171671597 171704365).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13103 171671597 171704365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171573293 171638829).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 171573293 ≤ 171606061)
    (by decide : 171606061 ≤ 171638829) block0 block1

theorem join_0_1 : (twinPrimeSegment 171638829 171704365).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 171638829 ≤ 171671597)
    (by decide : 171671597 ≤ 171704365) block2 block3

theorem join_1_0 : (twinPrimeSegment 171573293 171704365).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 171573293 ≤ 171638829)
    (by decide : 171638829 ≤ 171704365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171573293 171704365).card = 473 := join_1_0

end S081C13
end Sude.GeneratedTwinScan
