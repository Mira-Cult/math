import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22055)) 486408237 486441005 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486408237 486441005).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22055 486408237 486441005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22056)) 486441005 486473773 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486441005 486473773).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22056 486441005 486473773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22056)) 486473773 486506541 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486473773 486506541).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22056 486473773 486506541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22057)) 486506541 486539309 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 486506541 486539309).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22057 486506541 486539309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486408237 486473773).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 486408237 ≤ 486441005)
    (by decide : 486441005 ≤ 486473773) block0 block1

theorem join_0_1 : (twinPrimeSegment 486473773 486539309).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 486473773 ≤ 486506541)
    (by decide : 486506541 ≤ 486539309) block2 block3

theorem join_1_0 : (twinPrimeSegment 486408237 486539309).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 486408237 ≤ 486473773)
    (by decide : 486473773 ≤ 486539309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486408237 486539309).card = 454 := join_1_0

end S231C15
end Sude.GeneratedTwinScan
