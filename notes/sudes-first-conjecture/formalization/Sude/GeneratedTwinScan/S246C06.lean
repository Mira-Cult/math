import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22731)) 516685869 516718637 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516685869 516718637).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22731 516685869 516718637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22732)) 516718637 516751405 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516718637 516751405).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22732 516718637 516751405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22732)) 516751405 516784173 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 516751405 516784173).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22732 516751405 516784173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22733)) 516784173 516816941 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 516784173 516816941).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22733 516784173 516816941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516685869 516751405).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 516685869 ≤ 516718637)
    (by decide : 516718637 ≤ 516751405) block0 block1

theorem join_0_1 : (twinPrimeSegment 516751405 516816941).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 516751405 ≤ 516784173)
    (by decide : 516784173 ≤ 516816941) block2 block3

theorem join_1_0 : (twinPrimeSegment 516685869 516816941).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 516685869 ≤ 516751405)
    (by decide : 516751405 ≤ 516816941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516685869 516816941).card = 418 := join_1_0

end S246C06
end Sude.GeneratedTwinScan
