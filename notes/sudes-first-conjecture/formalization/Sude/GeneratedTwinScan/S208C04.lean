import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20898)) 436731949 436764717 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436731949 436764717).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20898 436731949 436764717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20899)) 436764717 436797485 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436764717 436797485).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20899 436764717 436797485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20900)) 436797485 436830253 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436797485 436830253).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20900 436797485 436830253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20901)) 436830253 436863021 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436830253 436863021).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20901 436830253 436863021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436731949 436797485).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 436731949 ≤ 436764717)
    (by decide : 436764717 ≤ 436797485) block0 block1

theorem join_0_1 : (twinPrimeSegment 436797485 436863021).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 436797485 ≤ 436830253)
    (by decide : 436830253 ≤ 436863021) block2 block3

theorem join_1_0 : (twinPrimeSegment 436731949 436863021).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 436731949 ≤ 436797485)
    (by decide : 436797485 ≤ 436863021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436731949 436863021).card = 484 := join_1_0

end S208C04
end Sude.GeneratedTwinScan
