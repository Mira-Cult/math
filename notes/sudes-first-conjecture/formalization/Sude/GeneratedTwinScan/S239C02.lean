import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22394)) 501481517 501514285 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501481517 501514285).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22394 501481517 501514285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22395)) 501514285 501547053 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501514285 501547053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22395 501514285 501547053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22395)) 501547053 501579821 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501547053 501579821).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22395 501547053 501579821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22396)) 501579821 501612589 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501579821 501612589).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22396 501579821 501612589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501481517 501547053).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 501481517 ≤ 501514285)
    (by decide : 501514285 ≤ 501547053) block0 block1

theorem join_0_1 : (twinPrimeSegment 501547053 501612589).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 501547053 ≤ 501579821)
    (by decide : 501579821 ≤ 501612589) block2 block3

theorem join_1_0 : (twinPrimeSegment 501481517 501612589).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 501481517 ≤ 501547053)
    (by decide : 501547053 ≤ 501612589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501481517 501612589).card = 454 := join_1_0

end S239C02
end Sude.GeneratedTwinScan
