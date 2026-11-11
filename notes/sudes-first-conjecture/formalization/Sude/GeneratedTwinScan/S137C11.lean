import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16993)) 288751661 288784429 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288751661 288784429).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16993 288751661 288784429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16994)) 288784429 288817197 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288784429 288817197).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16994 288784429 288817197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16995)) 288817197 288849965 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288817197 288849965).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16995 288817197 288849965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16996)) 288849965 288882733 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288849965 288882733).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16996 288849965 288882733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288751661 288817197).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 288751661 ≤ 288784429)
    (by decide : 288784429 ≤ 288817197) block0 block1

theorem join_0_1 : (twinPrimeSegment 288817197 288882733).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 288817197 ≤ 288849965)
    (by decide : 288849965 ≤ 288882733) block2 block3

theorem join_1_0 : (twinPrimeSegment 288751661 288882733).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 288751661 ≤ 288817197)
    (by decide : 288817197 ≤ 288882733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288751661 288882733).card = 464 := join_1_0

end S137C11
end Sude.GeneratedTwinScan
