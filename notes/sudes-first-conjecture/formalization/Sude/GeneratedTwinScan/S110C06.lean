import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15215)) 231473197 231505965 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231473197 231505965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15215 231473197 231505965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15216)) 231505965 231538733 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231505965 231538733).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15216 231505965 231538733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15217)) 231538733 231571501 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231538733 231571501).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15217 231538733 231571501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15218)) 231571501 231604269 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231571501 231604269).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15218 231571501 231604269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231473197 231538733).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 231473197 ≤ 231505965)
    (by decide : 231505965 ≤ 231538733) block0 block1

theorem join_0_1 : (twinPrimeSegment 231538733 231604269).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 231538733 ≤ 231571501)
    (by decide : 231571501 ≤ 231604269) block2 block3

theorem join_1_0 : (twinPrimeSegment 231473197 231604269).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 231473197 ≤ 231538733)
    (by decide : 231538733 ≤ 231604269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231473197 231604269).card = 444 := join_1_0

end S110C06
end Sude.GeneratedTwinScan
