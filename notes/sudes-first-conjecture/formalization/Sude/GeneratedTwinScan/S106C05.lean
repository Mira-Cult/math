import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14932)) 222953517 222986285 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222953517 222986285).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14932 222953517 222986285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14933)) 222986285 223019053 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222986285 223019053).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14933 222986285 223019053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14934)) 223019053 223051821 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223019053 223051821).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14934 223019053 223051821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14936)) 223051821 223084589 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223051821 223084589).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14936 223051821 223084589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222953517 223019053).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 222953517 ≤ 222986285)
    (by decide : 222986285 ≤ 223019053) block0 block1

theorem join_0_1 : (twinPrimeSegment 223019053 223084589).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 223019053 ≤ 223051821)
    (by decide : 223051821 ≤ 223084589) block2 block3

theorem join_1_0 : (twinPrimeSegment 222953517 223084589).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 222953517 ≤ 223019053)
    (by decide : 223019053 ≤ 223084589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222953517 223084589).card = 491 := join_1_0

end S106C05
end Sude.GeneratedTwinScan
