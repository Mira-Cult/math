import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20300)) 412090413 412123181 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 412090413 412123181).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20300 412090413 412123181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20301)) 412123181 412155949 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 412123181 412155949).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20301 412123181 412155949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20302)) 412155949 412188717 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412155949 412188717).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20302 412155949 412188717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20303)) 412188717 412221485 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412188717 412221485).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20303 412188717 412221485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 412090413 412155949).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 412090413 ≤ 412123181)
    (by decide : 412123181 ≤ 412155949) block0 block1

theorem join_0_1 : (twinPrimeSegment 412155949 412221485).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 412155949 ≤ 412188717)
    (by decide : 412188717 ≤ 412221485) block2 block3

theorem join_1_0 : (twinPrimeSegment 412090413 412221485).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 412090413 ≤ 412155949)
    (by decide : 412155949 ≤ 412221485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 412090413 412221485).card = 447 := join_1_0

end S196C08
end Sude.GeneratedTwinScan
