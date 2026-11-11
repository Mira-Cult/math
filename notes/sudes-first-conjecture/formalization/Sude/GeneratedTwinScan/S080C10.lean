import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13004)) 169082925 169115693 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169082925 169115693).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13004 169082925 169115693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13005)) 169115693 169148461 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169115693 169148461).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13005 169115693 169148461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13006)) 169148461 169181229 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169148461 169181229).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13006 169148461 169181229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13008)) 169181229 169213997 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169181229 169213997).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13008 169181229 169213997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169082925 169148461).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 169082925 ≤ 169115693)
    (by decide : 169115693 ≤ 169148461) block0 block1

theorem join_0_1 : (twinPrimeSegment 169148461 169213997).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 169148461 ≤ 169181229)
    (by decide : 169181229 ≤ 169213997) block2 block3

theorem join_1_0 : (twinPrimeSegment 169082925 169213997).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 169082925 ≤ 169148461)
    (by decide : 169148461 ≤ 169213997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169082925 169213997).card = 474 := join_1_0

end S080C10
end Sude.GeneratedTwinScan
