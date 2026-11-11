import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22344)) 499253293 499286061 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 499253293 499286061).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22344 499253293 499286061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22345)) 499286061 499318829 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 499286061 499318829).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22345 499286061 499318829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22346)) 499318829 499351597 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 499318829 499351597).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22346 499318829 499351597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22346)) 499351597 499384365 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 499351597 499384365).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22346 499351597 499384365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 499253293 499318829).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 499253293 ≤ 499286061)
    (by decide : 499286061 ≤ 499318829) block0 block1

theorem join_0_1 : (twinPrimeSegment 499318829 499384365).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 499318829 ≤ 499351597)
    (by decide : 499351597 ≤ 499384365) block2 block3

theorem join_1_0 : (twinPrimeSegment 499253293 499384365).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 499253293 ≤ 499318829)
    (by decide : 499318829 ≤ 499384365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 499253293 499384365).card = 426 := join_1_0

end S238C01
end Sude.GeneratedTwinScan
