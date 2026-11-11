import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20132)) 405274669 405307437 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405274669 405307437).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20132 405274669 405307437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20133)) 405307437 405340205 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405307437 405340205).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20133 405307437 405340205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20133)) 405340205 405372973 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405340205 405372973).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20133 405340205 405372973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20134)) 405372973 405405741 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 405372973 405405741).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20134 405372973 405405741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405274669 405340205).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 405274669 ≤ 405307437)
    (by decide : 405307437 ≤ 405340205) block0 block1

theorem join_0_1 : (twinPrimeSegment 405340205 405405741).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 405340205 ≤ 405372973)
    (by decide : 405372973 ≤ 405405741) block2 block3

theorem join_1_0 : (twinPrimeSegment 405274669 405405741).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 405274669 ≤ 405340205)
    (by decide : 405340205 ≤ 405405741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405274669 405405741).card = 432 := join_1_0

end S193C04
end Sude.GeneratedTwinScan
