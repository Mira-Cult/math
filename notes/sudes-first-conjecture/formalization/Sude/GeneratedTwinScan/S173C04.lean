import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19062)) 363331629 363364397 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363331629 363364397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19062 363331629 363364397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19062)) 363364397 363397165 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363364397 363397165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19062 363364397 363397165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19063)) 363397165 363429933 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363397165 363429933).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19063 363397165 363429933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19064)) 363429933 363462701 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363429933 363462701).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19064 363429933 363462701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363331629 363397165).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 363331629 ≤ 363364397)
    (by decide : 363364397 ≤ 363397165) block0 block1

theorem join_0_1 : (twinPrimeSegment 363397165 363462701).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 363397165 ≤ 363429933)
    (by decide : 363429933 ≤ 363462701) block2 block3

theorem join_1_0 : (twinPrimeSegment 363331629 363462701).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 363331629 ≤ 363397165)
    (by decide : 363397165 ≤ 363462701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363331629 363462701).card = 470 := join_1_0

end S173C04
end Sude.GeneratedTwinScan
