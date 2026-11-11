import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17514)) 306708525 306741293 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306708525 306741293).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17514 306708525 306741293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17514)) 306741293 306774061 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306741293 306774061).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17514 306741293 306774061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17515)) 306774061 306806829 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306774061 306806829).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17515 306774061 306806829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17516)) 306806829 306839597 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306806829 306839597).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17516 306806829 306839597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306708525 306774061).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 306708525 ≤ 306741293)
    (by decide : 306741293 ≤ 306774061) block0 block1

theorem join_0_1 : (twinPrimeSegment 306774061 306839597).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 306774061 ≤ 306806829)
    (by decide : 306806829 ≤ 306839597) block2 block3

theorem join_1_0 : (twinPrimeSegment 306708525 306839597).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 306708525 ≤ 306774061)
    (by decide : 306774061 ≤ 306839597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306708525 306839597).card = 469 := join_1_0

end S146C04
end Sude.GeneratedTwinScan
