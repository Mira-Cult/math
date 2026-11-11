import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16328)) 266600493 266633261 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 266600493 266633261).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16328 266600493 266633261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16329)) 266633261 266666029 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 266633261 266666029).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16329 266633261 266666029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16330)) 266666029 266698797 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 266666029 266698797).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16330 266666029 266698797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16331)) 266698797 266731565 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 266698797 266731565).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16331 266698797 266731565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 266600493 266666029).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 266600493 ≤ 266633261)
    (by decide : 266633261 ≤ 266666029) block0 block1

theorem join_0_1 : (twinPrimeSegment 266666029 266731565).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 266666029 ≤ 266698797)
    (by decide : 266698797 ≤ 266731565) block2 block3

theorem join_1_0 : (twinPrimeSegment 266600493 266731565).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 266600493 ≤ 266666029)
    (by decide : 266666029 ≤ 266731565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 266600493 266731565).card = 465 := join_1_0

end S127C02
end Sude.GeneratedTwinScan
