import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14373)) 206569517 206602285 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 206569517 206602285).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14373 206569517 206602285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14374)) 206602285 206635053 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 206602285 206635053).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14374 206602285 206635053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14375)) 206635053 206667821 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 206635053 206667821).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14375 206635053 206667821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14377)) 206667821 206700589 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 206667821 206700589).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14377 206667821 206700589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 206569517 206635053).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 206569517 ≤ 206602285)
    (by decide : 206602285 ≤ 206635053) block0 block1

theorem join_0_1 : (twinPrimeSegment 206635053 206700589).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 206635053 ≤ 206667821)
    (by decide : 206667821 ≤ 206700589) block2 block3

theorem join_1_0 : (twinPrimeSegment 206569517 206700589).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 206569517 ≤ 206635053)
    (by decide : 206635053 ≤ 206700589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 206569517 206700589).card = 448 := join_1_0

end S098C08
end Sude.GeneratedTwinScan
