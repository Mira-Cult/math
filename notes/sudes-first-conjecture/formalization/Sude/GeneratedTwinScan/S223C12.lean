import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21662)) 469237805 469270573 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469237805 469270573).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21662 469237805 469270573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21663)) 469270573 469303341 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469270573 469303341).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21663 469270573 469303341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21664)) 469303341 469336109 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469303341 469336109).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21664 469303341 469336109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21664)) 469336109 469368877 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469336109 469368877).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21664 469336109 469368877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469237805 469303341).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 469237805 ≤ 469270573)
    (by decide : 469270573 ≤ 469303341) block0 block1

theorem join_0_1 : (twinPrimeSegment 469303341 469368877).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 469303341 ≤ 469336109)
    (by decide : 469336109 ≤ 469368877) block2 block3

theorem join_1_0 : (twinPrimeSegment 469237805 469368877).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 469237805 ≤ 469303341)
    (by decide : 469303341 ≤ 469368877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469237805 469368877).card = 429 := join_1_0

end S223C12
end Sude.GeneratedTwinScan
