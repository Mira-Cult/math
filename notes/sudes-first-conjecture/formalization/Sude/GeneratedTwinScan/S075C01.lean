import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12547)) 157417517 157450285 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157417517 157450285).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12547 157417517 157450285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12549)) 157450285 157483053 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157450285 157483053).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12549 157450285 157483053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12550)) 157483053 157515821 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 157483053 157515821).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12550 157483053 157515821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12551)) 157515821 157548589 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 157515821 157548589).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12551 157515821 157548589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157417517 157483053).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 157417517 ≤ 157450285)
    (by decide : 157450285 ≤ 157483053) block0 block1

theorem join_0_1 : (twinPrimeSegment 157483053 157548589).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 157483053 ≤ 157515821)
    (by decide : 157515821 ≤ 157548589) block2 block3

theorem join_1_0 : (twinPrimeSegment 157417517 157548589).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 157417517 ≤ 157483053)
    (by decide : 157483053 ≤ 157548589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157417517 157548589).card = 477 := join_1_0

end S075C01
end Sude.GeneratedTwinScan
