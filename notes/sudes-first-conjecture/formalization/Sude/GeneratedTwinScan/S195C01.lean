import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20226)) 409075757 409108525 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409075757 409108525).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20226 409075757 409108525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20227)) 409108525 409141293 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 409108525 409141293).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20227 409108525 409141293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20228)) 409141293 409174061 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409141293 409174061).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20228 409141293 409174061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20228)) 409174061 409206829 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409174061 409206829).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20228 409174061 409206829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409075757 409141293).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 409075757 ≤ 409108525)
    (by decide : 409108525 ≤ 409141293) block0 block1

theorem join_0_1 : (twinPrimeSegment 409141293 409206829).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 409141293 ≤ 409174061)
    (by decide : 409174061 ≤ 409206829) block2 block3

theorem join_1_0 : (twinPrimeSegment 409075757 409206829).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 409075757 ≤ 409141293)
    (by decide : 409141293 ≤ 409206829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409075757 409206829).card = 450 := join_1_0

end S195C01
end Sude.GeneratedTwinScan
