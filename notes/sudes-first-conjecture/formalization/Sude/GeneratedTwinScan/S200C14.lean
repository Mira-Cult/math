import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20525)) 421265453 421298221 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421265453 421298221).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20525 421265453 421298221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20526)) 421298221 421330989 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421298221 421330989).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20526 421298221 421330989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20527)) 421330989 421363757 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421330989 421363757).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20527 421330989 421363757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20527)) 421363757 421396525 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421363757 421396525).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20527 421363757 421396525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421265453 421330989).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 421265453 ≤ 421298221)
    (by decide : 421298221 ≤ 421330989) block0 block1

theorem join_0_1 : (twinPrimeSegment 421330989 421396525).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 421330989 ≤ 421363757)
    (by decide : 421363757 ≤ 421396525) block2 block3

theorem join_1_0 : (twinPrimeSegment 421265453 421396525).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 421265453 ≤ 421330989)
    (by decide : 421330989 ≤ 421396525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421265453 421396525).card = 416 := join_1_0

end S200C14
end Sude.GeneratedTwinScan
