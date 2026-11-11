import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16452)) 270663725 270696493 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270663725 270696493).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16452 270663725 270696493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16453)) 270696493 270729261 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270696493 270729261).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16453 270696493 270729261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16454)) 270729261 270762029 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270729261 270762029).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16454 270729261 270762029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16455)) 270762029 270794797 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 270762029 270794797).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16455 270762029 270794797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270663725 270729261).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 270663725 ≤ 270696493)
    (by decide : 270696493 ≤ 270729261) block0 block1

theorem join_0_1 : (twinPrimeSegment 270729261 270794797).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 270729261 ≤ 270762029)
    (by decide : 270762029 ≤ 270794797) block2 block3

theorem join_1_0 : (twinPrimeSegment 270663725 270794797).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 270663725 ≤ 270729261)
    (by decide : 270729261 ≤ 270794797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270663725 270794797).card = 473 := join_1_0

end S129C01
end Sude.GeneratedTwinScan
