import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14577)) 212467757 212500525 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212467757 212500525).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14577 212467757 212500525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14578)) 212500525 212533293 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212500525 212533293).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14578 212500525 212533293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14579)) 212533293 212566061 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212533293 212566061).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14579 212533293 212566061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14580)) 212566061 212598829 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212566061 212598829).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14580 212566061 212598829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212467757 212533293).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 212467757 ≤ 212500525)
    (by decide : 212500525 ≤ 212533293) block0 block1

theorem join_0_1 : (twinPrimeSegment 212533293 212598829).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 212533293 ≤ 212566061)
    (by decide : 212566061 ≤ 212598829) block2 block3

theorem join_1_0 : (twinPrimeSegment 212467757 212598829).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 212467757 ≤ 212533293)
    (by decide : 212533293 ≤ 212598829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212467757 212598829).card = 484 := join_1_0

end S101C05
end Sude.GeneratedTwinScan
