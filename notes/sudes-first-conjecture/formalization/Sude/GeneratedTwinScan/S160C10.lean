import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18354)) 336855085 336887853 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336855085 336887853).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18354 336855085 336887853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18355)) 336887853 336920621 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 336887853 336920621).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18355 336887853 336920621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18356)) 336920621 336953389 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336920621 336953389).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18356 336920621 336953389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18357)) 336953389 336986157 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336953389 336986157).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18357 336953389 336986157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336855085 336920621).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 336855085 ≤ 336887853)
    (by decide : 336887853 ≤ 336920621) block0 block1

theorem join_0_1 : (twinPrimeSegment 336920621 336986157).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 336920621 ≤ 336953389)
    (by decide : 336953389 ≤ 336986157) block2 block3

theorem join_1_0 : (twinPrimeSegment 336855085 336986157).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 336855085 ≤ 336920621)
    (by decide : 336920621 ≤ 336986157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336855085 336986157).card = 447 := join_1_0

end S160C10
end Sude.GeneratedTwinScan
