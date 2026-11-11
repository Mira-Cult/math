import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21846)) 477233197 477265965 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 477233197 477265965).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21846 477233197 477265965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21847)) 477265965 477298733 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477265965 477298733).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21847 477265965 477298733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21847)) 477298733 477331501 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477298733 477331501).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21847 477298733 477331501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21848)) 477331501 477364269 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477331501 477364269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21848 477331501 477364269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 477233197 477298733).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 477233197 ≤ 477265965)
    (by decide : 477265965 ≤ 477298733) block0 block1

theorem join_0_1 : (twinPrimeSegment 477298733 477364269).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 477298733 ≤ 477331501)
    (by decide : 477331501 ≤ 477364269) block2 block3

theorem join_1_0 : (twinPrimeSegment 477233197 477364269).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 477233197 ≤ 477298733)
    (by decide : 477298733 ≤ 477364269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 477233197 477364269).card = 415 := join_1_0

end S227C09
end Sude.GeneratedTwinScan
