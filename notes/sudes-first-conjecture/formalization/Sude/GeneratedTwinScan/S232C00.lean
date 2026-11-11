import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22058)) 486539309 486572077 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486539309 486572077).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22058 486539309 486572077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22059)) 486572077 486604845 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486572077 486604845).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22059 486572077 486604845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22059)) 486604845 486637613 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486604845 486637613).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22059 486604845 486637613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22060)) 486637613 486670381 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 486637613 486670381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22060 486637613 486670381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486539309 486604845).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 486572077)
    (by decide : 486572077 ≤ 486604845) block0 block1

theorem join_0_1 : (twinPrimeSegment 486604845 486670381).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 486604845 ≤ 486637613)
    (by decide : 486637613 ≤ 486670381) block2 block3

theorem join_1_0 : (twinPrimeSegment 486539309 486670381).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 486604845)
    (by decide : 486604845 ≤ 486670381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486539309 486670381).card = 431 := join_1_0

end S232C00
end Sude.GeneratedTwinScan
