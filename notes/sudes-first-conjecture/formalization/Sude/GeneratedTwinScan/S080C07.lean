import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12989)) 168689709 168722477 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168689709 168722477).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12989 168689709 168722477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12990)) 168722477 168755245 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168722477 168755245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12990 168722477 168755245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12991)) 168755245 168788013 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168755245 168788013).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12991 168755245 168788013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12993)) 168788013 168820781 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168788013 168820781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12993 168788013 168820781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168689709 168755245).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 168689709 ≤ 168722477)
    (by decide : 168722477 ≤ 168755245) block0 block1

theorem join_0_1 : (twinPrimeSegment 168755245 168820781).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 168755245 ≤ 168788013)
    (by decide : 168788013 ≤ 168820781) block2 block3

theorem join_1_0 : (twinPrimeSegment 168689709 168820781).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 168689709 ≤ 168755245)
    (by decide : 168755245 ≤ 168820781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168689709 168820781).card = 463 := join_1_0

end S080C07
end Sude.GeneratedTwinScan
