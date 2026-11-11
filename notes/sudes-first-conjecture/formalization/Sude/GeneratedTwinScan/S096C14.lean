import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14254)) 203161645 203194413 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203161645 203194413).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14254 203161645 203194413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14255)) 203194413 203227181 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203194413 203227181).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14255 203194413 203227181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14256)) 203227181 203259949 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203227181 203259949).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14256 203227181 203259949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14258)) 203259949 203292717 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203259949 203292717).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14258 203259949 203292717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203161645 203227181).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 203161645 ≤ 203194413)
    (by decide : 203194413 ≤ 203227181) block0 block1

theorem join_0_1 : (twinPrimeSegment 203227181 203292717).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 203227181 ≤ 203259949)
    (by decide : 203259949 ≤ 203292717) block2 block3

theorem join_1_0 : (twinPrimeSegment 203161645 203292717).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 203161645 ≤ 203227181)
    (by decide : 203227181 ≤ 203292717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203161645 203292717).card = 460 := join_1_0

end S096C14
end Sude.GeneratedTwinScan
