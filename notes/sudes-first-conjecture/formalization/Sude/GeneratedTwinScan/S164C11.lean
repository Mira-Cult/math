import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18585)) 345374765 345407533 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345374765 345407533).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18585 345374765 345407533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18586)) 345407533 345440301 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345407533 345440301).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18586 345407533 345440301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18586)) 345440301 345473069 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345440301 345473069).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18586 345440301 345473069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18587)) 345473069 345505837 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345473069 345505837).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18587 345473069 345505837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345374765 345440301).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 345374765 ≤ 345407533)
    (by decide : 345407533 ≤ 345440301) block0 block1

theorem join_0_1 : (twinPrimeSegment 345440301 345505837).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 345440301 ≤ 345473069)
    (by decide : 345473069 ≤ 345505837) block2 block3

theorem join_1_0 : (twinPrimeSegment 345374765 345505837).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 345374765 ≤ 345440301)
    (by decide : 345440301 ≤ 345505837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345374765 345505837).card = 432 := join_1_0

end S164C11
end Sude.GeneratedTwinScan
