import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21428)) 459145261 459178029 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 459145261 459178029).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21428 459145261 459178029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21429)) 459178029 459210797 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 459178029 459210797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21429 459178029 459210797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21429)) 459210797 459243565 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 459210797 459243565).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21429 459210797 459243565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21430)) 459243565 459276333 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 459243565 459276333).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21430 459243565 459276333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 459145261 459210797).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 459145261 ≤ 459178029)
    (by decide : 459178029 ≤ 459210797) block0 block1

theorem join_0_1 : (twinPrimeSegment 459210797 459276333).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 459210797 ≤ 459243565)
    (by decide : 459243565 ≤ 459276333) block2 block3

theorem join_1_0 : (twinPrimeSegment 459145261 459276333).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 459145261 ≤ 459210797)
    (by decide : 459210797 ≤ 459276333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 459145261 459276333).card = 433 := join_1_0

end S218C15
end Sude.GeneratedTwinScan
