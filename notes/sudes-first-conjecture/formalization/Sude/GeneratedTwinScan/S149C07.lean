import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17703)) 313393197 313425965 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 313393197 313425965).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17703 313393197 313425965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17704)) 313425965 313458733 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313425965 313458733).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17704 313425965 313458733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17705)) 313458733 313491501 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313458733 313491501).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17705 313458733 313491501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17706)) 313491501 313524269 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 313491501 313524269).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17706 313491501 313524269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 313393197 313458733).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 313393197 ≤ 313425965)
    (by decide : 313425965 ≤ 313458733) block0 block1

theorem join_0_1 : (twinPrimeSegment 313458733 313524269).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 313458733 ≤ 313491501)
    (by decide : 313491501 ≤ 313524269) block2 block3

theorem join_1_0 : (twinPrimeSegment 313393197 313524269).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 313393197 ≤ 313458733)
    (by decide : 313458733 ≤ 313524269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 313393197 313524269).card = 431 := join_1_0

end S149C07
end Sude.GeneratedTwinScan
