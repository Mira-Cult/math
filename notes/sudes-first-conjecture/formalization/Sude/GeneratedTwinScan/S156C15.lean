import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18142)) 329121837 329154605 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329121837 329154605).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18142 329121837 329154605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18143)) 329154605 329187373 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329154605 329187373).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18143 329154605 329187373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18144)) 329187373 329220141 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329187373 329220141).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18144 329187373 329220141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18145)) 329220141 329252909 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329220141 329252909).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18145 329220141 329252909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329121837 329187373).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 329121837 ≤ 329154605)
    (by decide : 329154605 ≤ 329187373) block0 block1

theorem join_0_1 : (twinPrimeSegment 329187373 329252909).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 329187373 ≤ 329220141)
    (by decide : 329220141 ≤ 329252909) block2 block3

theorem join_1_0 : (twinPrimeSegment 329121837 329252909).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 329121837 ≤ 329187373)
    (by decide : 329187373 ≤ 329252909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329121837 329252909).card = 430 := join_1_0

end S156C15
end Sude.GeneratedTwinScan
