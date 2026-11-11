import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13129)) 172359725 172392493 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172359725 172392493).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13129 172359725 172392493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13131)) 172392493 172425261 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172392493 172425261).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13131 172392493 172425261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13132)) 172425261 172458029 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172425261 172458029).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13132 172425261 172458029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13133)) 172458029 172490797 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172458029 172490797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13133 172458029 172490797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172359725 172425261).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 172359725 ≤ 172392493)
    (by decide : 172392493 ≤ 172425261) block0 block1

theorem join_0_1 : (twinPrimeSegment 172425261 172490797).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 172425261 ≤ 172458029)
    (by decide : 172458029 ≤ 172490797) block2 block3

theorem join_1_0 : (twinPrimeSegment 172359725 172490797).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 172359725 ≤ 172425261)
    (by decide : 172425261 ≤ 172490797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172359725 172490797).card = 482 := join_1_0

end S082C03
end Sude.GeneratedTwinScan
