import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21302)) 453771309 453804077 = 78 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453771309 453804077).card = 78 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21302 453771309 453804077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21303)) 453804077 453836845 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453804077 453836845).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21303 453804077 453836845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21304)) 453836845 453869613 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453836845 453869613).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21304 453836845 453869613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21304)) 453869613 453902381 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453869613 453902381).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21304 453869613 453902381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453771309 453836845).card = 185 := by
  simpa using combineTwinPrimeSegments (by decide : 453771309 ≤ 453804077)
    (by decide : 453804077 ≤ 453836845) block0 block1

theorem join_0_1 : (twinPrimeSegment 453836845 453902381).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 453836845 ≤ 453869613)
    (by decide : 453869613 ≤ 453902381) block2 block3

theorem join_1_0 : (twinPrimeSegment 453771309 453902381).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 453771309 ≤ 453836845)
    (by decide : 453836845 ≤ 453902381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453771309 453902381).card = 406 := join_1_0

end S216C06
end Sude.GeneratedTwinScan
