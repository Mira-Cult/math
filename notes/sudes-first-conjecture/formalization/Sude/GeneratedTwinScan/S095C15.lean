import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14185)) 201195565 201228333 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 201195565 201228333).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14185 201195565 201228333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14186)) 201228333 201261101 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 201228333 201261101).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14186 201228333 201261101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14187)) 201261101 201293869 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 201261101 201293869).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14187 201261101 201293869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14188)) 201293869 201326637 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 201293869 201326637).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14188 201293869 201326637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 201195565 201261101).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 201195565 ≤ 201228333)
    (by decide : 201228333 ≤ 201261101) block0 block1

theorem join_0_1 : (twinPrimeSegment 201261101 201326637).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 201261101 ≤ 201293869)
    (by decide : 201293869 ≤ 201326637) block2 block3

theorem join_1_0 : (twinPrimeSegment 201195565 201326637).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 201195565 ≤ 201261101)
    (by decide : 201261101 ≤ 201326637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 201195565 201326637).card = 456 := join_1_0

end S095C15
end Sude.GeneratedTwinScan
