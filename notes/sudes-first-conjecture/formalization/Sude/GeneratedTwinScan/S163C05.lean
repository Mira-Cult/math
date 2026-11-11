import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18507)) 342491181 342523949 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 342491181 342523949).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18507 342491181 342523949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18508)) 342523949 342556717 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 342523949 342556717).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18508 342523949 342556717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18509)) 342556717 342589485 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342556717 342589485).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18509 342556717 342589485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18510)) 342589485 342622253 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342589485 342622253).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18510 342589485 342622253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 342491181 342556717).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 342491181 ≤ 342523949)
    (by decide : 342523949 ≤ 342556717) block0 block1

theorem join_0_1 : (twinPrimeSegment 342556717 342622253).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 342556717 ≤ 342589485)
    (by decide : 342589485 ≤ 342622253) block2 block3

theorem join_1_0 : (twinPrimeSegment 342491181 342622253).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 342491181 ≤ 342556717)
    (by decide : 342556717 ≤ 342622253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 342491181 342622253).card = 439 := join_1_0

end S163C05
end Sude.GeneratedTwinScan
