import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22514)) 506855469 506888237 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506855469 506888237).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22514 506855469 506888237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22514)) 506888237 506921005 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 506888237 506921005).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22514 506888237 506921005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22515)) 506921005 506953773 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506921005 506953773).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22515 506921005 506953773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22516)) 506953773 506986541 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506953773 506986541).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22516 506953773 506986541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506855469 506921005).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 506855469 ≤ 506888237)
    (by decide : 506888237 ≤ 506921005) block0 block1

theorem join_0_1 : (twinPrimeSegment 506921005 506986541).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 506921005 ≤ 506953773)
    (by decide : 506953773 ≤ 506986541) block2 block3

theorem join_1_0 : (twinPrimeSegment 506855469 506986541).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 506855469 ≤ 506921005)
    (by decide : 506921005 ≤ 506986541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506855469 506986541).card = 417 := join_1_0

end S241C11
end Sude.GeneratedTwinScan
