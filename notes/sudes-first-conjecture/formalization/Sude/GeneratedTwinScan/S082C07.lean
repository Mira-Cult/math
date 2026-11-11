import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13149)) 172884013 172916781 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172884013 172916781).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13149 172884013 172916781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13151)) 172916781 172949549 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172916781 172949549).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13151 172916781 172949549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13152)) 172949549 172982317 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172949549 172982317).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13152 172949549 172982317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13153)) 172982317 173015085 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172982317 173015085).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13153 172982317 173015085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172884013 172949549).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 172884013 ≤ 172916781)
    (by decide : 172916781 ≤ 172949549) block0 block1

theorem join_0_1 : (twinPrimeSegment 172949549 173015085).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 172949549 ≤ 172982317)
    (by decide : 172982317 ≤ 173015085) block2 block3

theorem join_1_0 : (twinPrimeSegment 172884013 173015085).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 172884013 ≤ 172949549)
    (by decide : 172949549 ≤ 173015085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172884013 173015085).card = 478 := join_1_0

end S082C07
end Sude.GeneratedTwinScan
