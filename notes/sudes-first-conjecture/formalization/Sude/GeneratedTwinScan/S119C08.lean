import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15831)) 250609709 250642477 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250609709 250642477).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15831 250609709 250642477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15832)) 250642477 250675245 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250642477 250675245).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15832 250642477 250675245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15833)) 250675245 250708013 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250675245 250708013).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15833 250675245 250708013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15834)) 250708013 250740781 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250708013 250740781).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15834 250708013 250740781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250609709 250675245).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 250609709 ≤ 250642477)
    (by decide : 250642477 ≤ 250675245) block0 block1

theorem join_0_1 : (twinPrimeSegment 250675245 250740781).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 250675245 ≤ 250708013)
    (by decide : 250708013 ≤ 250740781) block2 block3

theorem join_1_0 : (twinPrimeSegment 250609709 250740781).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 250609709 ≤ 250675245)
    (by decide : 250675245 ≤ 250740781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250609709 250740781).card = 451 := join_1_0

end S119C08
end Sude.GeneratedTwinScan
