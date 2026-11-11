import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20845)) 434503725 434536493 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 434503725 434536493).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20845 434503725 434536493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20846)) 434536493 434569261 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 434536493 434569261).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20846 434536493 434569261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20847)) 434569261 434602029 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 434569261 434602029).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20847 434569261 434602029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20847)) 434602029 434634797 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 434602029 434634797).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20847 434602029 434634797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 434503725 434569261).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 434503725 ≤ 434536493)
    (by decide : 434536493 ≤ 434569261) block0 block1

theorem join_0_1 : (twinPrimeSegment 434569261 434634797).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 434569261 ≤ 434602029)
    (by decide : 434602029 ≤ 434634797) block2 block3

theorem join_1_0 : (twinPrimeSegment 434503725 434634797).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 434503725 ≤ 434569261)
    (by decide : 434569261 ≤ 434634797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 434503725 434634797).card = 432 := join_1_0

end S207C03
end Sude.GeneratedTwinScan
