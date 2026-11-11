import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18996)) 360841261 360874029 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360841261 360874029).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18996 360841261 360874029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18997)) 360874029 360906797 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360874029 360906797).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18997 360874029 360906797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18998)) 360906797 360939565 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360906797 360939565).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18998 360906797 360939565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18999)) 360939565 360972333 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360939565 360972333).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18999 360939565 360972333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360841261 360906797).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 360841261 ≤ 360874029)
    (by decide : 360874029 ≤ 360906797) block0 block1

theorem join_0_1 : (twinPrimeSegment 360906797 360972333).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 360906797 ≤ 360939565)
    (by decide : 360939565 ≤ 360972333) block2 block3

theorem join_1_0 : (twinPrimeSegment 360841261 360972333).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 360841261 ≤ 360906797)
    (by decide : 360906797 ≤ 360972333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360841261 360972333).card = 446 := join_1_0

end S172C01
end Sude.GeneratedTwinScan
