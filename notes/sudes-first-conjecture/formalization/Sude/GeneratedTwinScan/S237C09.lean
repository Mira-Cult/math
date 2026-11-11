import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22321)) 498204717 498237485 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498204717 498237485).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22321 498204717 498237485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22321)) 498237485 498270253 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498237485 498270253).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22321 498237485 498270253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22322)) 498270253 498303021 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498270253 498303021).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22322 498270253 498303021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22323)) 498303021 498335789 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498303021 498335789).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22323 498303021 498335789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498204717 498270253).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 498204717 ≤ 498237485)
    (by decide : 498237485 ≤ 498270253) block0 block1

theorem join_0_1 : (twinPrimeSegment 498270253 498335789).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 498270253 ≤ 498303021)
    (by decide : 498303021 ≤ 498335789) block2 block3

theorem join_1_0 : (twinPrimeSegment 498204717 498335789).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 498204717 ≤ 498270253)
    (by decide : 498270253 ≤ 498335789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498204717 498335789).card = 426 := join_1_0

end S237C09
end Sude.GeneratedTwinScan
