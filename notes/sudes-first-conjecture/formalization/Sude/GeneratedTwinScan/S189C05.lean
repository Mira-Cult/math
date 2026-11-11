import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19926)) 397017133 397049901 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397017133 397049901).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19926 397017133 397049901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19926)) 397049901 397082669 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397049901 397082669).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19926 397049901 397082669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19927)) 397082669 397115437 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397082669 397115437).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19927 397082669 397115437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19928)) 397115437 397148205 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397115437 397148205).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19928 397115437 397148205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397017133 397082669).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 397017133 ≤ 397049901)
    (by decide : 397049901 ≤ 397082669) block0 block1

theorem join_0_1 : (twinPrimeSegment 397082669 397148205).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 397082669 ≤ 397115437)
    (by decide : 397115437 ≤ 397148205) block2 block3

theorem join_1_0 : (twinPrimeSegment 397017133 397148205).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 397017133 ≤ 397082669)
    (by decide : 397082669 ≤ 397148205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397017133 397148205).card = 438 := join_1_0

end S189C05
end Sude.GeneratedTwinScan
