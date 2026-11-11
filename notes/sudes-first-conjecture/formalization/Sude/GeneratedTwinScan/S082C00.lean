import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13114)) 171966509 171999277 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171966509 171999277).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13114 171966509 171999277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13116)) 171999277 172032045 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171999277 172032045).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13116 171999277 172032045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13117)) 172032045 172064813 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172032045 172064813).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13117 172032045 172064813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13118)) 172064813 172097581 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172064813 172097581).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13118 172064813 172097581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171966509 172032045).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 171999277)
    (by decide : 171999277 ≤ 172032045) block0 block1

theorem join_0_1 : (twinPrimeSegment 172032045 172097581).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 172032045 ≤ 172064813)
    (by decide : 172064813 ≤ 172097581) block2 block3

theorem join_1_0 : (twinPrimeSegment 171966509 172097581).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 172032045)
    (by decide : 172032045 ≤ 172097581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171966509 172097581).card = 446 := join_1_0

end S082C00
end Sude.GeneratedTwinScan
