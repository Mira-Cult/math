import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14604)) 213254189 213286957 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 213254189 213286957).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14604 213254189 213286957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14605)) 213286957 213319725 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213286957 213319725).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14605 213286957 213319725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14606)) 213319725 213352493 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213319725 213352493).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14606 213319725 213352493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14607)) 213352493 213385261 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 213352493 213385261).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14607 213352493 213385261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 213254189 213319725).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 213254189 ≤ 213286957)
    (by decide : 213286957 ≤ 213319725) block0 block1

theorem join_0_1 : (twinPrimeSegment 213319725 213385261).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 213319725 ≤ 213352493)
    (by decide : 213352493 ≤ 213385261) block2 block3

theorem join_1_0 : (twinPrimeSegment 213254189 213385261).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 213254189 ≤ 213319725)
    (by decide : 213319725 ≤ 213385261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 213254189 213385261).card = 465 := join_1_0

end S101C11
end Sude.GeneratedTwinScan
