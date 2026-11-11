import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21726)) 471990317 472023085 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471990317 472023085).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21726 471990317 472023085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21726)) 472023085 472055853 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472023085 472055853).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21726 472023085 472055853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21727)) 472055853 472088621 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472055853 472088621).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21727 472055853 472088621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21728)) 472088621 472121389 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472088621 472121389).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21728 472088621 472121389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471990317 472055853).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 471990317 ≤ 472023085)
    (by decide : 472023085 ≤ 472055853) block0 block1

theorem join_0_1 : (twinPrimeSegment 472055853 472121389).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 472055853 ≤ 472088621)
    (by decide : 472088621 ≤ 472121389) block2 block3

theorem join_1_0 : (twinPrimeSegment 471990317 472121389).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 471990317 ≤ 472055853)
    (by decide : 472055853 ≤ 472121389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471990317 472121389).card = 430 := join_1_0

end S225C01
end Sude.GeneratedTwinScan
