import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17261)) 297926701 297959469 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297926701 297959469).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17261 297926701 297959469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17262)) 297959469 297992237 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297959469 297992237).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17262 297959469 297992237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17263)) 297992237 298025005 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297992237 298025005).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17263 297992237 298025005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17264)) 298025005 298057773 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298025005 298057773).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17264 298025005 298057773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297926701 297992237).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 297926701 ≤ 297959469)
    (by decide : 297959469 ≤ 297992237) block0 block1

theorem join_0_1 : (twinPrimeSegment 297992237 298057773).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 297992237 ≤ 298025005)
    (by decide : 298025005 ≤ 298057773) block2 block3

theorem join_1_0 : (twinPrimeSegment 297926701 298057773).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 297926701 ≤ 297992237)
    (by decide : 297992237 ≤ 298057773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297926701 298057773).card = 461 := join_1_0

end S142C01
end Sude.GeneratedTwinScan
