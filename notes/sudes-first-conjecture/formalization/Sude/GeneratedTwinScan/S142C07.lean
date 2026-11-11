import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17284)) 298713133 298745901 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298713133 298745901).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17284 298713133 298745901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17285)) 298745901 298778669 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298745901 298778669).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17285 298745901 298778669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17286)) 298778669 298811437 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298778669 298811437).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17286 298778669 298811437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17287)) 298811437 298844205 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298811437 298844205).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17287 298811437 298844205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298713133 298778669).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 298713133 ≤ 298745901)
    (by decide : 298745901 ≤ 298778669) block0 block1

theorem join_0_1 : (twinPrimeSegment 298778669 298844205).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 298778669 ≤ 298811437)
    (by decide : 298811437 ≤ 298844205) block2 block3

theorem join_1_0 : (twinPrimeSegment 298713133 298844205).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 298713133 ≤ 298778669)
    (by decide : 298778669 ≤ 298844205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298713133 298844205).card = 442 := join_1_0

end S142C07
end Sude.GeneratedTwinScan
