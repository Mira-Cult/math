import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16228)) 263323693 263356461 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263323693 263356461).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16228 263323693 263356461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16229)) 263356461 263389229 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263356461 263389229).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16229 263356461 263389229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16230)) 263389229 263421997 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263389229 263421997).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16230 263389229 263421997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16231)) 263421997 263454765 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263421997 263454765).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16231 263421997 263454765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263323693 263389229).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 263323693 ≤ 263356461)
    (by decide : 263356461 ≤ 263389229) block0 block1

theorem join_0_1 : (twinPrimeSegment 263389229 263454765).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 263389229 ≤ 263421997)
    (by decide : 263421997 ≤ 263454765) block2 block3

theorem join_1_0 : (twinPrimeSegment 263323693 263454765).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 263323693 ≤ 263389229)
    (by decide : 263389229 ≤ 263454765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263323693 263454765).card = 483 := join_1_0

end S125C09
end Sude.GeneratedTwinScan
