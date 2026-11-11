import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20779)) 431751213 431783981 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431751213 431783981).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20779 431751213 431783981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20780)) 431783981 431816749 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431783981 431816749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20780 431783981 431816749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20780)) 431816749 431849517 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431816749 431849517).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20780 431816749 431849517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20781)) 431849517 431882285 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431849517 431882285).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20781 431849517 431882285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431751213 431816749).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 431751213 ≤ 431783981)
    (by decide : 431783981 ≤ 431816749) block0 block1

theorem join_0_1 : (twinPrimeSegment 431816749 431882285).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 431816749 ≤ 431849517)
    (by decide : 431849517 ≤ 431882285) block2 block3

theorem join_1_0 : (twinPrimeSegment 431751213 431882285).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 431751213 ≤ 431816749)
    (by decide : 431816749 ≤ 431882285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431751213 431882285).card = 447 := join_1_0

end S205C14
end Sude.GeneratedTwinScan
