import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20403)) 416284717 416317485 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416284717 416317485).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20403 416284717 416317485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20404)) 416317485 416350253 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416317485 416350253).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20404 416317485 416350253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20405)) 416350253 416383021 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416350253 416383021).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20405 416350253 416383021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20406)) 416383021 416415789 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416383021 416415789).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20406 416383021 416415789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416284717 416350253).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 416284717 ≤ 416317485)
    (by decide : 416317485 ≤ 416350253) block0 block1

theorem join_0_1 : (twinPrimeSegment 416350253 416415789).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 416350253 ≤ 416383021)
    (by decide : 416383021 ≤ 416415789) block2 block3

theorem join_1_0 : (twinPrimeSegment 416284717 416415789).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 416284717 ≤ 416350253)
    (by decide : 416350253 ≤ 416415789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416284717 416415789).card = 427 := join_1_0

end S198C08
end Sude.GeneratedTwinScan
