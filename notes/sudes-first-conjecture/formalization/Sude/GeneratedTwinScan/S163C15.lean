import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18542)) 343801901 343834669 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 343801901 343834669).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18542 343801901 343834669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18543)) 343834669 343867437 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 343834669 343867437).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18543 343834669 343867437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18544)) 343867437 343900205 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 343867437 343900205).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18544 343867437 343900205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18545)) 343900205 343932973 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 343900205 343932973).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18545 343900205 343932973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 343801901 343867437).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 343801901 ≤ 343834669)
    (by decide : 343834669 ≤ 343867437) block0 block1

theorem join_0_1 : (twinPrimeSegment 343867437 343932973).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 343867437 ≤ 343900205)
    (by decide : 343900205 ≤ 343932973) block2 block3

theorem join_1_0 : (twinPrimeSegment 343801901 343932973).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 343801901 ≤ 343867437)
    (by decide : 343867437 ≤ 343932973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 343801901 343932973).card = 463 := join_1_0

end S163C15
end Sude.GeneratedTwinScan
