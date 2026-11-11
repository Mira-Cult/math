import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13445)) 180748333 180781101 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180748333 180781101).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13445 180748333 180781101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13446)) 180781101 180813869 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180781101 180813869).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13446 180781101 180813869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13447)) 180813869 180846637 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180813869 180846637).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13447 180813869 180846637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13449)) 180846637 180879405 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180846637 180879405).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13449 180846637 180879405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180748333 180813869).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 180748333 ≤ 180781101)
    (by decide : 180781101 ≤ 180813869) block0 block1

theorem join_0_1 : (twinPrimeSegment 180813869 180879405).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 180813869 ≤ 180846637)
    (by decide : 180846637 ≤ 180879405) block2 block3

theorem join_1_0 : (twinPrimeSegment 180748333 180879405).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 180748333 ≤ 180813869)
    (by decide : 180813869 ≤ 180879405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180748333 180879405).card = 453 := join_1_0

end S086C03
end Sude.GeneratedTwinScan
