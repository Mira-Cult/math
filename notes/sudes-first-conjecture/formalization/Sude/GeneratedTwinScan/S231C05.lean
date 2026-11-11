import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22025)) 485097517 485130285 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485097517 485130285).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22025 485097517 485130285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22026)) 485130285 485163053 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485130285 485163053).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22026 485130285 485163053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22027)) 485163053 485195821 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485163053 485195821).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22027 485163053 485195821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22027)) 485195821 485228589 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485195821 485228589).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22027 485195821 485228589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485097517 485163053).card = 185 := by
  simpa using combineTwinPrimeSegments (by decide : 485097517 ≤ 485130285)
    (by decide : 485130285 ≤ 485163053) block0 block1

theorem join_0_1 : (twinPrimeSegment 485163053 485228589).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 485163053 ≤ 485195821)
    (by decide : 485195821 ≤ 485228589) block2 block3

theorem join_1_0 : (twinPrimeSegment 485097517 485228589).card = 407 := by
  simpa using combineTwinPrimeSegments (by decide : 485097517 ≤ 485163053)
    (by decide : 485163053 ≤ 485228589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485097517 485228589).card = 407 := join_1_0

end S231C05
end Sude.GeneratedTwinScan
