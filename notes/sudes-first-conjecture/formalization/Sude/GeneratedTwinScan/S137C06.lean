import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16974)) 288096301 288129069 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288096301 288129069).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16974 288096301 288129069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16975)) 288129069 288161837 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288129069 288161837).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16975 288129069 288161837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16976)) 288161837 288194605 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288161837 288194605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16976 288161837 288194605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16977)) 288194605 288227373 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288194605 288227373).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16977 288194605 288227373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288096301 288161837).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 288096301 ≤ 288129069)
    (by decide : 288129069 ≤ 288161837) block0 block1

theorem join_0_1 : (twinPrimeSegment 288161837 288227373).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 288161837 ≤ 288194605)
    (by decide : 288194605 ≤ 288227373) block2 block3

theorem join_1_0 : (twinPrimeSegment 288096301 288227373).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 288096301 ≤ 288161837)
    (by decide : 288161837 ≤ 288227373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288096301 288227373).card = 462 := join_1_0

end S137C06
end Sude.GeneratedTwinScan
