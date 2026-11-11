import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16674)) 278003757 278036525 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278003757 278036525).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16674 278003757 278036525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16675)) 278036525 278069293 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278036525 278069293).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16675 278036525 278069293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16676)) 278069293 278102061 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278069293 278102061).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16676 278069293 278102061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16677)) 278102061 278134829 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278102061 278134829).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16677 278102061 278134829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278003757 278069293).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 278003757 ≤ 278036525)
    (by decide : 278036525 ≤ 278069293) block0 block1

theorem join_0_1 : (twinPrimeSegment 278069293 278134829).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 278069293 ≤ 278102061)
    (by decide : 278102061 ≤ 278134829) block2 block3

theorem join_1_0 : (twinPrimeSegment 278003757 278134829).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 278003757 ≤ 278069293)
    (by decide : 278069293 ≤ 278134829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278003757 278134829).card = 471 := join_1_0

end S132C09
end Sude.GeneratedTwinScan
