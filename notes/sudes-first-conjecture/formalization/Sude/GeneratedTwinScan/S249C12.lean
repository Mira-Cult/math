import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22886)) 523763757 523796525 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523763757 523796525).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22886 523763757 523796525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22887)) 523796525 523829293 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523796525 523829293).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22887 523796525 523829293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22888)) 523829293 523862061 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523829293 523862061).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22888 523829293 523862061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22888)) 523862061 523894829 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523862061 523894829).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22888 523862061 523894829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523763757 523829293).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 523763757 ≤ 523796525)
    (by decide : 523796525 ≤ 523829293) block0 block1

theorem join_0_1 : (twinPrimeSegment 523829293 523894829).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 523829293 ≤ 523862061)
    (by decide : 523862061 ≤ 523894829) block2 block3

theorem join_1_0 : (twinPrimeSegment 523763757 523894829).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 523763757 ≤ 523829293)
    (by decide : 523829293 ≤ 523894829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523763757 523894829).card = 465 := join_1_0

end S249C12
end Sude.GeneratedTwinScan
